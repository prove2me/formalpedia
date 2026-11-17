-- Prove2me | Theorems.Thm_IntQuotHNP_Supplement_theorem_5_2
-- name    : IntQuotHNP.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:06:11.078826+00:00
-- url     : https://prove2.me/theorems/556133b0-34cd-414d-b991-9ea1d87f8a3b
-- title:
--   Theorem 5.2 — EC-HNP recovery: Las Vegas exact output, cost $\mathrm{poly}_N(\log p)(1+\min\{X,\Delta_N,\Delta_N^{N/(3N-3)}\})$
-- statement:
--   This is the recovery theorem for the elliptic-curve hidden number problem.
--
--   For every polynomial-time restriction verifier there is one randomized machine (Algorithm 1 with the EC-HNP reconstructor and a preliminary check for infinity observations) such that, for every $N\ge5$:
--
--   1. **Las Vegas exactness.** On every promised admissible input, every halting run outputs exactly the set of points satisfying the input constraints, the machine halts with probability one with finite expected bit time, and this set (which contains $y^*$) has at most $2X$ elements.
--   2. **Lattice shape.** On finite inputs the $m=N(N+1)/2$ vectors $\Phi(P_h)$ of Lemma 5.3 are linearly independent and have $d=N(N+1)/2$ coordinates ($k=N$ error variables).
--   3. **Cost (12).** If $M\ge16N^2$ and $6X^2<p$, the expected bit time averaged over the accepted query tuples is at most
--   $$
--   \mathrm{poly}_N(\log p)\bigl(1+\min\{X,\Delta_N,\Delta_N^{N/(3N-3)}\}\bigr),\qquad \Delta_N=\frac{X^{5N-6}}{M^{N-2}} .
--   $$
--   4. **Polynomial window.** For fixed $A,c\ge0$, if $M\ge\max\{16N^2,p/(\log p)^c\}$ and $X\le p^{\rho_N}(\log p)^A$ with $\rho_N=(N-2)/(5N-6)$, this average is $\mathrm{poly}_{N,A,c}(\log p)$,
--   5. and in that window the output equals $\{y^*\}$ with probability $1-o(1)$ as $p\to\infty$.
--
--   Every bound holds for all primes $p>3$, nonsingular curves, generators $R_0$, hidden points $y^*$ and admissible approximation rules, with constants depending only on $N$ (and on $A,c$ in 4), and on the polynomial bounds of the verifier and of the input encoding.
--
--   **Formalization Note** $\mathrm{poly}_N(\log p)$ is $C(\log p)^K$ with $C,K$ chosen after $N$ and before $p$, the curve, $X$, $y^*$ and the rule. Powers with real exponents are real powers, and $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - reading: Algorithm 1, its (expected) bit time, Las Vegas and probability one → one randomized multi-tape Turing machine (MTMachine, alphabet Fin 8, one fair bit per tick); bit time = ticks, expected bit time = lower integral of the halting time under the fair-coin measure, probability one = almost surely; reason: the paper names no machine model; its bounds are linear in the number of tests, so the model may lose only a polylogarithmic factor on the proof's bookkeeping (balanced search trees), which multi-tape machines do and single-tape machines need not
--   - generalization: a promised subgroup or coset restriction on y∗, supplied with a polynomial-time verifier → any property decided by a deterministic verifier machine V with running time C_V(1 + |w|)^{K_V}, run on the input code followed by the point code; the machine M and the constants may depend on V, C_V, K_V; reason: the algorithm only calls the verifier and the analysis never uses the form of the restriction; subgroup and coset restrictions with their verifiers are instances
--   - generalization: leading-bit intervals with X a power of two → any integer intervals [v_i, u_i] with at most X canonical values, X arbitrary; reason: the intervals only add checks in the reconstructor; the power-of-two case is an instance
--   - reading: for fixed N, the total public encoding length is bounded by a fixed polynomial in log p → hypothesis: every sampled input has code length at most C_E(log p)^{K_E}; C, K may depend on C_E, K_E; reason: the bound is a standing assumption of Definition 5.1 on the inputs; the uniqueness clause does not need it
--   - encoding: Q_j − Q_i ∉ E[2], E[2] over an algebraic closure → 2 • (Q_j − Q_i) ≠ 0 in E(𝔽_p); reason: Q_j − Q_i lies in E(𝔽_p) and E(𝔽_p) → E(𝔽̄_p) is an injective homomorphism
--   - encoding: queries sampled independently and uniformly from G by scalar multiplication of R₀, tuples failing (11) rejected → uniform average over the accepted s ∈ (ℤ_M)^N, Q_i = s_i R₀, M the order of R₀; reason: s ↦ (s_i R₀) is a bijection onto G^N; rejection sampling gives the uniform law on accepted tuples
--   - encoding: input-averaged expected bit cost → finiteness of every sampled expected time, then the average of their real values; reason: the expected time lives in [0, ∞]; stating finiteness first excludes the junk value of the real conversion
--   - encoding: the output equals {y∗} with probability 1 − o(1) → for every η > 0 there is p₁ such that for primes p ≥ p₁ the probability that some point y ≠ y∗ satisfies the constraints is at most η; reason: by clause 1 the output is exactly the set of satisfying points, which contains y∗
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 5.2, p.30 (PDF p.31); Definition 5.1, pp.29–30 (PDF pp.30–31); Lemma 5.3, pp.30–31 (PDF pp.31–32)

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_IntQuotHNP_Sampling
import Definitions.Def_IntQuotHNP_Supplement_LasVegas
import Definitions.Def_IntQuotHNP_Supplement_CoeffMap
import Definitions.Def_IntQuotHNP_Supplement_Recovery
import Definitions.Def_IntQuotHNP_Supplement_ECHNP

namespace IntQuotHNP

namespace Supplement

open MeasureTheory OAI.MatchingFPRAS

/-- **Theorem 5.2 (EC-HNP recovery).**
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 5.2, p.30 (PDF p.31): "For
fixed N ≥ 5, Algorithm 1, with the reconstructor below and a preliminary check for infinity
observations, is Las Vegas and returns exactly the points satisfying the input constraints on every
admissible promised input. Its output contains y∗ and has at most 2X elements. On finite inputs, it
uses k = N error variables and a lattice of rank m = N(N + 1)/2 in ambient dimension d = m. If
M ≥ 16N² and 6X² < p, its input-averaged expected bit cost is
poly_N(log p)(1 + min{X, ∆_N, ∆_N^{N/(3N−3)}}), ∆_N = X^{5N−6}/M^{N−2}. (12) In particular, fix
A, c ≥ 0 and put ρ_N = (N − 2)/(5N − 6). If M ≥ max{16N², p/(log p)^c} and X ≤ p^{ρ_N}(log p)^A,
the expected cost is poly_{N,A,c}(log p) and the output equals {y∗} with probability 1 − o(1) as
p → ∞. These guarantees hold uniformly for every fixed y∗ and every approximation rule in the
sampling model above."

For every polynomial-time restriction verifier `V` (bound `C_V(1 + |w|)^{K_V}`) there is one
randomized machine `M` such that:
1. on every promised admissible input `I`, the set of points satisfying the input constraints has
   at most `2X` elements, every halting run of `M` outputs exactly that set, `M` halts with
   probability one, and its expected bit time is finite (Las Vegas);
2. on every promised admissible finite input, the `N(N + 1)/2` vectors `Φ(P_h)` of Lemma 5.3 are
   linearly independent and there are `N(N + 1)/2` distinct nonconstant monomials (`k = N`,
   `m = d = N(N + 1)/2`);
3. (12): for every `N ≥ 5` and every encoding-length bound `C_E(log p)^{K_E}` there are `C, K` such
   that for every prime `p > 3`, nonsingular curve, generator `R₀` of order `M ≥ 16N²`, `X ≥ 1`
   with `6X² < p`, restriction description, hidden point `y∗` and admissible rule whose sampled
   inputs have length at most `C_E(log p)^{K_E}`: every sampled input has finite expected time, and
   the average expected bit time over the accepted query tuples is at most
   `C(log p)^K (1 + min{X, Δ_N, Δ_N^{N/(3N−3)}})`;
4. for every `N ≥ 5`, `C_E, K_E` and `A, c ≥ 0` there are `C, K` bounding that average by
   `C(log p)^K` whenever `M ≥ max{16N², p/(log p)^c}`, `1 ≤ X < p` and `X ≤ p^{ρ_N}(log p)^A`;
5. for every `N ≥ 5`, `A, c ≥ 0` and `η > 0`, for all sufficiently large primes `p` in that range,
   the probability over accepted tuples that some point other than `y∗` satisfies the input
   constraints (that the output differs from `{y∗}`) is at most `η`.

**Formalization Note.** "Algorithm 1" is read as one randomized multi-tape Turing machine
(`MTMachine`, as in Theorem 3.4), chosen after the verifier and before `N`, `A`, `c`, `p`, the
curve, `X`, `y∗` and the rule. Las Vegas: every halting run is correct, and halting is almost sure
with finite expected time. The restriction is the property decided by the verifier `V` on the input
code followed by the point; the trivial and the subgroup or coset restrictions are instances. The
paper's "the total public encoding length … is bounded by a fixed polynomial in log p" is the
hypothesis on the sampled inputs' code length; the constants may depend on it and on the
verifier's bound. Input averages and probabilities are the published `avg`, `prob` over the accepted
tuples `s ∈ (ℤ_M)^N` (`Q_i = s_i R₀`), with infinity observations retained. Expected bit time is in
`ℝ≥0∞`; its finiteness is stated before it is averaged as a real number. `log` is the natural
logarithm, and the real powers are `Real.rpow`. -/
theorem theorem_5_2 :
    ∀ (V : MTMachine) (CV : ℝ) (KV : ℕ), IsVerifier V CV KV →
    ∃ M : MTMachine,
      (∀ (p : ℕ) [Fact p.Prime] (I : ECInput p), ECPromised V I → ECAdmissible I →
        ∃ s : Finset (ecCurve I.aE I.bE).Point, (∀ y, y ∈ s ↔ ECSatisfies V I y) ∧
          s.card ≤ 2 * I.X ∧ AlwaysOutputs M (ecEncodeInput I) (encodePointSet s) ∧
          (∀ᵐ ω ∂coinMeasure, haltTime M (ecEncodeInput I) ω ≠ ⊤) ∧
          expectedTime M (ecEncodeInput I) ≠ ⊤) ∧
      (∀ (p : ℕ) [Fact p.Prime] (I : ECInput p), ECPromised V I → ECAdmissible I → ECFinite I →
        LinearIndependent ℝ (fun h => Phi I.X (ecPolys I) (ecPolys I h)) ∧
          Fintype.card (ECIdx I.N) = I.N * (I.N + 1) / 2 ∧
          (mons (ecPolys I)).card = I.N * (I.N + 1) / 2) ∧
      (∀ N : ℕ, 5 ≤ N → ∀ (CE : ℝ) (KE : ℕ), ∃ (C : ℝ) (K : ℕ),
        ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ aE bE : ZMod p, 4 * aE ^ 3 + 27 * bE ^ 2 ≠ 0 →
        ∀ R0 : (ecCurve aE bE).Point, 16 * N ^ 2 ≤ addOrderOf R0 →
        ∀ X : ℕ, 1 ≤ X → 6 * X ^ 2 < p →
        ∀ (restr : List Bool) (y : (ecCurve aE bE).Point) (rule : ECRule R0 N),
          ECIsRule V R0 N X restr y rule →
          (∀ s ∈ ecAccepted R0 N,
            ((ecEncodeInput (ecSampled R0 N X restr y rule s)).length : ℝ) ≤
              CE * Real.log p ^ KE) →
          (∀ s ∈ ecAccepted R0 N,
            expectedTime M (ecEncodeInput (ecSampled R0 N X restr y rule s)) ≠ ⊤) ∧
          avg (ecAccepted R0 N)
              (fun s => (expectedTime M (ecEncodeInput (ecSampled R0 N X restr y rule s))).toReal) ≤
            C * Real.log p ^ K *
              (1 + min (X : ℝ) (min (ecDelta N X (addOrderOf R0))
                (ecDelta N X (addOrderOf R0) ^ ((N : ℝ) / (3 * N - 3)))))) ∧
      (∀ N : ℕ, 5 ≤ N → ∀ (CE : ℝ) (KE : ℕ) (A c : ℝ), 0 ≤ A → 0 ≤ c → ∃ (C : ℝ) (K : ℕ),
        ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ aE bE : ZMod p, 4 * aE ^ 3 + 27 * bE ^ 2 ≠ 0 →
        ∀ R0 : (ecCurve aE bE).Point, (16 * N ^ 2 : ℝ) ≤ addOrderOf R0 →
          (p : ℝ) / Real.log p ^ c ≤ addOrderOf R0 →
        ∀ X : ℕ, 1 ≤ X → X < p → (X : ℝ) ≤ (p : ℝ) ^ rhoN N * Real.log p ^ A →
        ∀ (restr : List Bool) (y : (ecCurve aE bE).Point) (rule : ECRule R0 N),
          ECIsRule V R0 N X restr y rule →
          (∀ s ∈ ecAccepted R0 N,
            ((ecEncodeInput (ecSampled R0 N X restr y rule s)).length : ℝ) ≤
              CE * Real.log p ^ KE) →
          avg (ecAccepted R0 N)
              (fun s => (expectedTime M (ecEncodeInput (ecSampled R0 N X restr y rule s))).toReal) ≤
            C * Real.log p ^ K) ∧
      (∀ N : ℕ, 5 ≤ N → ∀ (A c : ℝ), 0 ≤ A → 0 ≤ c → ∀ η : ℝ, 0 < η → ∃ p₁ : ℕ,
        ∀ (p : ℕ) [Fact p.Prime], p₁ ≤ p → 3 < p → ∀ aE bE : ZMod p,
          4 * aE ^ 3 + 27 * bE ^ 2 ≠ 0 →
        ∀ R0 : (ecCurve aE bE).Point, (16 * N ^ 2 : ℝ) ≤ addOrderOf R0 →
          (p : ℝ) / Real.log p ^ c ≤ addOrderOf R0 →
        ∀ X : ℕ, 1 ≤ X → X < p → (X : ℝ) ≤ (p : ℝ) ^ rhoN N * Real.log p ^ A →
        ∀ (restr : List Bool) (y : (ecCurve aE bE).Point) (rule : ECRule R0 N),
          ECIsRule V R0 N X restr y rule →
          prob (ecAccepted R0 N)
              (fun s => ∃ y', y' ≠ y ∧ ECSatisfies V (ecSampled R0 N X restr y rule s) y') ≤
            η) := by sorry

end Supplement

end IntQuotHNP
