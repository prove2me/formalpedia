-- Prove2me | Theorems.Thm_MixScale_theorem_A_2
-- name    : MixScale.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:12:53.292052+00:00
-- url     : https://prove2.me/theorems/0b559910-d7cb-4160-bdb6-449293ecd3e1
-- title:
--   Theorem A.2, p.14 — known-profile learning, bound (15)
-- statement:
--   Under (2) and Definition A.1 (with $\chi$ a radial characteristic function in the dimension at hand), for $0<\varepsilon\le1$ and $0<\delta<1/2$, one global polynomial-time program attains $D_{\mathrm{par}}\le\varepsilon$ with probability at least $1-\delta$ using
--
--   $$N\le\mathsf P\Big[\gamma^{-2q}+\mathcal L_q(1/\gamma)\big\{\gamma^{-(2q+2-\tau)}+\gamma^{-(2q+2\alpha-\tau)}\varepsilon^{-2}\big\}\Big]\log\frac{\mathsf P'(\gamma^{-1})}{\delta}$$
--
--   samples, where $\tau=\min(q,1)$. This is the general upper bound of Appendices A–D, from which the free-weight rate of Theorem 1.1 follows on $\varepsilon\le\gamma/8$.
--
--   Differences from the source:
--   - reading: a global polynomial-time algorithm in "the real-arithmetic model" with "elementary function evaluation" and effective profile access (p.3, p.48), no instruction list → a MixScale.Machine program: real RAM core with rational literals, √, exp, log, cos, sin, fair coins, standard Gaussian draws, sample (cost d) and an adversarial profile oracle (cost ⌈evalC(1+1/η)^evalD⌉), with profile constants as inputs; reason: the paper names the model only; Gaussian draws are used in (43); the oracle is item 3 of Definition A.1
--   - reading: polynomial time → on every run, work ≤ C_T(C γ⁻¹ ε⁻¹ log(2/δ))^{D_T}; reason: the count on p.48 is O(dNQ) with N, Q ∝ log(1/δ), so log(1/δ) is the honest variable; time polynomial in 1/δ would be weaker
--   - reading: uses N ≤ … samples → the sample bound holds on every run and every admissible oracle, not in expectation; reason: "All branches have a predetermined polynomial operation budget" (p.48)
--   - reading: returns Θ̂; "The output must be a valid mixture" (p.2); in the equal-weight class, all mixing weights equal 1/k → on every run the output is legal, and has all weights 1/k for W = eq; reason: task definition on p.2, Algorithm 1 "A legal k-component tuple", and the fallback on p.48 and p.50
--   - encoding: P and P′(γ⁻¹) → C₀(dkBκ/w★)^D and C₀′(dkBκ/(w★γ))^{D′}, chosen after the profile, before all other parameters; reason: every variable is ≥ 1 on the inputs, so each form bounds the other
--   - encoding: P_Θ = Σ w_j P_{μ_j,Σ_j} with characteristic function (1) → the guarantee holds for every family of probability measures with characteristic function (1), mixed with weights w_j; reason: the family is unique by uniqueness of characteristic functions and exists (checked in the sanity file)
--   - encoding: with probability at least 1 − δ → ∃ measurable E ⊆ {success} with 1 − δ ≤ P(E); reason: avoids outer measure; equal to the ordinary probability when the success set is measurable
--   - encoding: d, k given (implicitly positive) → 0 < d and 0 < k; reason: dimension and component count are positive throughout; only degenerate inputs are excluded
--   - generalization: χ a radial characteristic function "in every dimension under consideration" → the hypothesis IsRadialCF χ d only for the dimension d at hand, with the program chosen before d; reason: a profile radial in every dimension satisfies it for each d, so this specializes to the paper
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Theorem A.2, p.14 (PDF p.16), (15)

import Mathlib
import Definitions.Def_MixScale_Laws

namespace MixScale

/-- **Theorem A.2** (Known-profile learning).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Theorem A.2, p.14 (PDF p.16), bound (15).

**Formalization Note.** The same shape as `UpperLaw S .free` under Definition A.1 only, with `ε ≤ 1`
and the bound (15). `P′(γ⁻¹)` is a polynomial in `C` and `γ⁻¹`, written `C₀′ (condC/γ)^{D′}`. -/
theorem theorem_A_2 (S : ProfileSpec) (hS : IsEffectiveProfile S) :
    ∃ (P : Program) (C₀ C₀' CT : ℝ) (D D' DT : ℕ),
      Admissible P ∧ 0 < C₀ ∧ 0 < C₀' ∧ 0 < CT ∧
      LearnsOn S .free P (fun _ => 1)
        (fun d k B κ wstar γ ε δ =>
          CT * (condC d k B κ wstar / γ / ε * Real.log (2 / δ)) ^ DT)
        (fun d k B κ wstar γ ε δ =>
          C₀ * condC d k B κ wstar ^ D *
            (γ ^ (-(2 * S.q)) + Lcal S.q (1 / γ) *
              (γ ^ (-(2 * S.q + 2 - min S.q 1)) +
                γ ^ (-(2 * S.q + 2 * S.α - min S.q 1)) * ε ^ (-2 : ℝ))) *
            Real.log (C₀' * (condC d k B κ wstar / γ) ^ D' / δ)) := by sorry

end MixScale
