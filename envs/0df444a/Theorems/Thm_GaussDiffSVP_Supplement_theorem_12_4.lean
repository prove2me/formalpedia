-- Prove2me | Theorems.Thm_GaussDiffSVP_Supplement_theorem_12_4
-- name    : GaussDiffSVP.Supplement.theorem_12_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:52:21.707768+00:00
-- url     : https://prove2.me/theorems/00059673-1053-47ee-8e91-12bf5f2edfd7
-- title:
--   Theorem 12.4 — GapSVP$_\gamma$ from reusable decoding with $2^{c(r,\gamma)n}$ queries
-- statement:
--   Assume an $r$-BDD interface as in §12.3 ($0<r<1/2$, preprocessing $P$, query work $D$, space $S$, good advice with probability at least $9/10$, fixed resource bounds outside the promise). Fix $\gamma>1$ with $r\gamma>1/2$, and put
--   $$c(r,\gamma)=-\frac12\log_2\Big(1-\frac1{4r^2\gamma^2}\Big).\tag{131}$$
--   There is a randomized algorithm that, given a basis of $L$ and $d>0$, distinguishes $\lambda_1(L)\le d$ from $\lambda_1(L)\ge\gamma d$ with success probability at least $2/3$, in time $\mathrm{poly}(n,B)[P+2^{c(r,\gamma)n}D]$ and space $S+\mathrm{poly}(n,B)$.
--
--   With the batch decoder of Theorem 12.1 this gives 4.15-GapSVP at the BDGL exponents (Corollary 12.5).
--
--   **Formalization Note** The input word is the basis followed by the rational $d$; the answer is the word $[1]$ (YES) or $[0]$ (NO), and the correct answer has probability at least $2/3$ on every YES and every NO instance.
--
--   Differences from the source:
--   - encoding: randomized word RAM, time in word operations, space in bits → the published randomized log-cost rational RAM TwMSOCount.Main, bit time and bit space; reason: App. C.1.1 (p.80): the same leading exponents hold with bit costs; the convention of the published goal
--   - reading: "Assume an r-BDD interface with 0 < r < 1/2 … With probability at least 9/10 …" (§12.3, p.59) → hypothesis IsBDDInterface r Pre Q P D S K (9/10) with 0 < r < 1/2, for every n ≥ 1 and every nonsingular rational basis; reason: the standing assumption of §12.3, stated once for the section
--   - encoding: poly(n, B) and "S + poly(n, B)" → (ℓ+1)^{K'} with K' and the program fixed after the fixed parameters and the interface, before the input; space (S(n)+1)(ℓ+1)^{K'}; reason: S already suppresses polynomial factors (it is S(n) times (ℓ+1)^K in the interface)
--   - reading: time and space bounds of the reduction → on every coin tape for every nonsingular input, also outside the promise; reason: "All resource bounds hold on every execution" (p.6, p.80); the stronger reading
--   - encoding: a decision "distinguishing λ₁(L) ≤ d from λ₁(L) ≥ γd" → input word encBasis B ++ [d] with rational d > 0, output word [1] for YES and [0] for NO; reason: a fixed encoding of the promise problem; d is part of the GapSVP input
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 12.4, p.60 ((131), p.60; §12.3 interface, p.59; proof App. F.3, p.105)

import Mathlib
import Definitions.Def_GaussDiffSVP_Supplement_BDD

open MeasureTheory TwMSOCount.Main CosetTreeSVP.SVP
open scoped ENNReal

namespace GaussDiffSVP.Supplement

/-- Theorem 12.4 (GapSVP from reusable decoding) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.60), under the standing assumption of
§12.3 (p.59): an `r`-BDD interface with `0 < r < 1/2`, preprocessing `P`, query work `D`, space
`S`, whose advice is good with probability at least `9/10` and whose query function has a fixed
resource bound even outside the promise.

Fix `γ > 1` with `rγ > 1/2`, and put `c(r, γ) = −½ log₂(1 − 1/(4r²γ²))` (131). There is a
randomized algorithm distinguishing `λ₁(L) ≤ d` from `λ₁(L) ≥ γd` with success probability at least
`2/3`, time `poly(n, B)[P + 2^{c(r,γ)n} D]`, and space `S + poly(n, B)`.

**Formalization Note.** The input word is the basis followed by the rational `d > 0`; the answer is
the output word `[1]` (YES, `λ₁ ≤ d`) or `[0]` (NO, `λ₁ ≥ γd`); on each YES and each NO instance the
correct answer has probability at least `2/3`. `P'` and `K'` may depend on `γ`, `r`, the
interface's programs and `K`, and are fixed before the input; `poly(n, B)` is `(ℓ+1)^{K'}` with `ℓ`
the bit length of the input word, and the resource bounds hold on every coin tape for every input
(also outside the promise). -/
theorem theorem_12_4 (r : ℝ) (hr0 : 0 < r) (hr : r < 1 / 2) (Pre Q : Program)
    (P D S : ℕ → ℝ) (K : ℕ) (hI : IsBDDInterface r Pre Q P D S K (fun _ => 9 / 10))
    (γ : ℝ) (hγ : 1 < γ) (hrγ : 1 / 2 < r * γ) :
    ∃ (P' : Program) (K' : ℕ), ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
      ∀ d : ℚ, 0 < d →
      (∀ τ : ℕ → Bool, ∃ s : RunStats,
        runStats P' τ (Config.init (SuperlatSVP.encBasis B ++ [d])) = some s ∧
        (s.time : ℝ) ≤ ((wordBits (SuperlatSVP.encBasis B ++ [d]) : ℝ) + 1) ^ K' *
          (P n + (2 : ℝ) ^ (-(1 / 2) * Real.logb 2 (1 - 1 / (4 * r ^ 2 * γ ^ 2)) * n) * D n) ∧
        (s.space : ℝ) ≤ (S n + 1) * ((wordBits (SuperlatSVP.encBasis B ++ [d]) : ℝ) + 1) ^ K') ∧
      (SuperlatSVP.lam1 (latQ B) ≤ d →
        (2 / 3 : ℝ≥0∞) ≤
          coinTape {τ | callOutput P' (Config.init (SuperlatSVP.encBasis B ++ [d])) τ = some [1]}) ∧
      (γ * d ≤ SuperlatSVP.lam1 (latQ B) →
        (2 / 3 : ℝ≥0∞) ≤
          coinTape {τ | callOutput P' (Config.init (SuperlatSVP.encBasis B ++ [d])) τ = some [0]}) := by sorry

end GaussDiffSVP.Supplement
