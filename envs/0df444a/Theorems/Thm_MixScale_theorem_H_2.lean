-- Prove2me | Theorems.Thm_MixScale_theorem_H_2
-- name    : MixScale.theorem_H_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:13:06.271559+00:00
-- url     : https://prove2.me/theorems/b14c1cff-0ae0-4436-ae08-eb7fd6139e3c
-- title:
--   Theorem H.2, pp.49–50 — global equal-weight upper bound, bound (96)
-- statement:
--   Under Definition A.1, (2) and the promise $w_j=1/k$, for $0<\varepsilon\le\gamma/8$ and $0<\delta<1/2$, one global randomized polynomial-time program attains $D_{\mathrm{par}}\le\varepsilon$ with probability at least $1-\delta$ using
--
--   $$N\le\mathsf P\,\ell_q(\gamma)\gamma^{-(2q-\tau)}\varepsilon^{-2}\log(\mathsf P'/\delta)$$
--
--   samples, where $\mathsf P,\mathsf P'$ are fixed-degree polynomials in $(d,k,B,\kappa)$. The polynomials contain no $\gamma^{-1},\varepsilon^{-1}$. This is the upper bound of Theorem 1.1 for equal weights, and it needs no regularity beyond Definition A.1.
--
--   Differences from the source:
--   - reading: a global polynomial-time algorithm in "the real-arithmetic model" with "elementary function evaluation" and effective profile access (p.3, p.48), no instruction list → a MixScale.Machine program: real RAM core with rational literals, √, exp, log, cos, sin, fair coins, standard Gaussian draws, sample (cost d) and an adversarial profile oracle (cost ⌈evalC(1+1/η)^evalD⌉), with profile constants as inputs; reason: the paper names the model only; Gaussian draws are used in (43); the oracle is item 3 of Definition A.1
--   - reading: polynomial time → on every run, work ≤ C_T(dkBκ γ⁻¹ ε⁻¹ log(2/δ))^{D_T}, with no w★⁻¹; reason: the promise makes w★ = 1/k available; the count on p.48 is O(dNQ) with N, Q ∝ log(1/δ)
--   - reading: uses N ≤ … samples → the sample bound holds on every run and every admissible oracle, not in expectation; reason: "All branches have a predetermined polynomial operation budget" (p.48)
--   - reading: returns Θ̂; "The output must be a valid mixture" (p.2); in the equal-weight class, all mixing weights equal 1/k → on every run the output is legal, and has all weights 1/k for W = eq; reason: task definition on p.2, Algorithm 1 "A legal k-component tuple", and the fallback on p.48 and p.50
--   - encoding: P, P′ fixed-degree polynomials in (d, k, B, κ) → C₀(dkBκ)^D and C₀′(dkBκ)^{D′}, chosen after the profile, before all other parameters; reason: every variable is ≥ 1 on the inputs
--   - encoding: P_Θ = Σ w_j P_{μ_j,Σ_j} with characteristic function (1) → the guarantee holds for every family of probability measures with characteristic function (1), mixed with weights w_j; reason: the family is unique by uniqueness of characteristic functions and exists (checked in the sanity file)
--   - encoding: with probability at least 1 − δ → ∃ measurable E ⊆ {success} with 1 − δ ≤ P(E); reason: avoids outer measure; equal to the ordinary probability when the success set is measurable
--   - encoding: d, k given (implicitly positive) → 0 < d and 0 < k; reason: dimension and component count are positive throughout; only degenerate inputs are excluded
--   - generalization: χ a radial characteristic function "in every dimension under consideration" → the hypothesis IsRadialCF χ d only for the dimension d at hand, with the program chosen before d; reason: a profile radial in every dimension satisfies it for each d, so this specializes to the paper
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Theorem H.2, pp.49–50 (PDF pp.51–52), (96)

import Mathlib
import Definitions.Def_MixScale_Laws

namespace MixScale

/-- **Theorem H.2** (Global equal-weight upper bound).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Theorem H.2, pp.49–50 (PDF pp.51–52), bound (96).

**Formalization Note.** The shape of `UpperLaw S .eq` under Definition A.1 only, with `P, P′` (and
the work bound) polynomials in `(d, k, B, κ)`, as printed: no `w★⁻¹` appears (the promise `w_j = 1/k`
makes `w★ = 1/k` available). `w★` remains a parameter of (2) in `LearnsOn`, unused by the budgets. -/
theorem theorem_H_2 (S : ProfileSpec) (hS : IsEffectiveProfile S) :
    ∃ (P : Program) (C₀ C₀' CT : ℝ) (D D' DT : ℕ),
      Admissible P ∧ 0 < C₀ ∧ 0 < C₀' ∧ 0 < CT ∧
      LearnsOn S .eq P (fun γ => γ / 8)
        (fun d k B κ _ γ ε δ =>
          CT * ((d : ℝ) * k * B * κ / γ / ε * Real.log (2 / δ)) ^ DT)
        (fun d k B κ _ γ ε δ =>
          C₀ * ((d : ℝ) * k * B * κ) ^ D * ellq S.q γ * γ ^ (-(2 * S.q - min S.q 1)) *
            ε ^ (-2 : ℝ) * Real.log (C₀' * ((d : ℝ) * k * B * κ) ^ D' / δ)) := by sorry

end MixScale
