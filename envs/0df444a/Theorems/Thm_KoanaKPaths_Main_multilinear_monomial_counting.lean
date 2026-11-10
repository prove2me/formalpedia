-- Prove2me | Theorems.Thm_KoanaKPaths_Main_multilinear_monomial_counting
-- name    : KoanaKPaths.Main.multilinear_monomial_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:37:45.308854+00:00
-- url     : https://prove2.me/theorems/1b1d2552-7b62-41fc-a4b2-fe7275535e2d
-- title:
--   Theorem 2 — approximate counting of multilinear monomials of right-skew circuits in $O^*(2^k\varepsilon^{-2}\log(1/\delta))$ time
-- statement:
--   Let $P$ be a noncommutative 0–1 polynomial of degree $k\ge1$ computed by a homogeneous 0–1 right-skew circuit $C$, and let $N(P)$ be the number of its multilinear monomials. For $0<\varepsilon,\delta<1$ there is a randomized algorithm that, given $C$, returns $\widehat N$ such that
--   $$\Pr\bigl[\,|\widehat N-N(P)|\le\varepsilon\,N(P)\,\bigr]\ge1-\delta$$
--   and runs in $O^*(2^k\varepsilon^{-2}\log(1/\delta))$ time, where $O^*$ suppresses factors polynomial in $k$ and the encoding size $L$ of $C$.
--
--   Precisely: there are one randomized machine $M$ and constants $K,c$, fixed before all inputs, such that for every such circuit and all real $\varepsilon,\delta\in(0,1)$, with $a=\lceil\log_2(1/\varepsilon)\rceil$, $b=\lceil\log_2(1/\delta)\rceil$, $L$ the encoding length of the circuit alone, excluding $a,b$ and
--   $$B=K\,2^k\,(1+k+L)^c\,4^a\,(b+1),$$
--   for every tape of more than $B$ fair random bits, every run halts within $B$ steps, reads at most $B$ random bits and writes a rational $\widehat N$; and over the random bits the displayed accuracy event has probability at least $1-\delta$.
--
--   This is the general counting theorem of the paper: Theorem 1 and the set-packing application follow by building suitable circuits.
--
--   **Formalization Note** The machine is a multi-stack Turing machine (Mathlib's `Turing.FinTM2` with finite alphabets, as in the reused fair-bit machine model), so a step is a bounded number of bit operations and the step count is bit time. Since $4^a<4\varepsilon^{-2}$, $B$ is at most a constant multiple of $2^k(1+k+L)^c\varepsilon^{-2}(1+\log(1/\delta))$. The degree $k$ is the syntactic degree of the output gate.
--
--   Differences from the source:
--   - encoding: a randomized algorithm running in O*(2^k ε^{-2} log(1/δ)) time → one fixed fair-bit FinTM2 machine and constants K, c chosen before all inputs, halting within K·2^k·(1+k+L)^c·4^a·(b+1) steps and random bits on every tape longer than that; reason: a FinTM2 step is a bounded fragment on finite alphabets, so steps are bit operations up to a constant, and O* hides exactly a polynomial in k and the circuit encoding length L, excluding the tolerance controls
--   - encoding: real ε, δ given to the algorithm → the machine reads a = ⌈log₂(1/ε)⌉ and b = ⌈log₂(1/δ)⌉ while accuracy and confidence are required for the real ε, δ themselves; reason: a machine cannot read a real number; 4^a < 4ε^{-2}, so every real tolerance is covered with the same ε^{-2} dependence
--   - reading: the factor log(1/δ) → the factor b + 1 ≤ 2 + log₂(1/δ), i.e. O(1 + log(1/δ)); reason: log(1/δ) tends to 0 as δ → 1, while any algorithm takes at least one sample, so the O-bound is read as O(1 + log(1/δ)), which is log(1/δ) up to a factor 3 for δ ≤ 1/2
--   - encoding: variables x_1, …, x_n and a DAG with a designated output → variables indexed by ℕ and a gate list in topological order with an output position; reason: a bijective relabeling; every DAG has a topological order
--   - reading: P of degree k → k is the syntactic degree of the output gate (P may be the zero polynomial); reason: Section 3 indexes the coefficients by [n]^k with k the output degree, and N(P) = 0 is allowed there
--   - encoding: the returned estimate N̂ → a written rational (binary numerator and positive denominator); reason: the algorithm's output is a rational number
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 3 (PDF p. 4), Theorem 2; repeated p. 5 (PDF p. 6), proved pp. 5–9 (PDF pp. 6–10)

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_KoanaKPaths_Main_Circuits
import Definitions.Def_KoanaKPaths_Main_Inputs

open HypergraphUnreliability.FPRAS

namespace KoanaKPaths.Main

/-- **Theorem 2** (Koana, STOC 2027 submission #953, printed p. 3 / PDF p. 4; repeated printed
p. 5 / PDF p. 6). One fair-bit machine `M` and constants `K, c`, fixed before all inputs, such
that for every homogeneous 0–1 right-skew circuit `C` whose output gate has degree `k ≥ 1`,
computing `P`, and all real `0 < ε, δ < 1`: on input `C` and the controls `a = ⌈log₂(1/ε)⌉`,
`b = ⌈log₂(1/δ)⌉`, for every tape of more than `B = K 2^k (1 + k + L)^c 4^a (b + 1)` fair bits
(`L` the circuit encoding length, excluding tolerance controls), every run halts within `B` steps using at most `B` tape
bits and writes a rational `N̂`, and `Pr[|N̂ − N(P)| ≤ ε N(P)] ≥ 1 − δ`. -/
theorem multilinear_monomial_counting :
    ∃ (M : CoinMachine) (K c : ℕ), ∀ (C : Circuit) (k : ℕ), C.IsHomZeroOne k → 1 ≤ k →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ T : ℕ, timeBudget K c k (circuitCode C).length (ctrl ε) (ctrl δ) < T →
        (∀ ω : Fin T → Bool, ∃ Nhat : Frac, 0 < Nhat.den ∧
          M.RunsWithin (circuitInput C ε δ) (tapeList ω)
            (timeBudget K c k (circuitCode C).length (ctrl ε) (ctrl δ)) (fracCode Nhat)) ∧
        1 - δ ≤ fairProb T (fun ω => ∃ Nhat : Frac, 0 < Nhat.den ∧
          M.RunsWithin (circuitInput C ε δ) (tapeList ω)
            (timeBudget K c k (circuitCode C).length (ctrl ε) (ctrl δ)) (fracCode Nhat) ∧
          |((Nhat.val : ℚ) : ℝ) - (numMultilinear C.outputPoly : ℝ)| ≤
            ε * (numMultilinear C.outputPoly : ℝ)) := by sorry

end KoanaKPaths.Main
