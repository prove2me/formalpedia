-- Prove2me | Theorems.Thm_OddGoldbach19_cosecant_bound_of_cotangent_sharp
-- name    : OddGoldbach19.cosecant_bound_of_cotangent_sharp
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:37:17.316336+00:00
-- url     : https://prove2.me/theorems/35404275-f578-4f24-a91d-3e8fdc5999b8
-- title:
--   Cotangent-to-cosecant transfer without a factor-three loss
-- statement:
--   Assume a real constant C bounds the cotangent quadratic form for every finite family of real frequencies with positive admissible circular gaps at most1, by C times the sum of squared complex coefficients divided by their gaps. Then, for every such family, the quadratic form with kernel pi/sin(pi*(theta_r-theta_s)) obeys the same bound with the same C. Both quadratic forms omit diagonal terms. Admissible circular gap means delta_r <= |theta_r-theta_s+m| for every distinct pair and every integer m. This is a conditional transfer theorem preserving the assumed constant; it does not itself assert that a particular cotangent bound holds.
-- source:
--   Antiperiodic two-copy transfer of the cotangent Hilbert form. Refinement of the transfer used in platform WeightedHilbert_circle_cosecant_bound_sixteen, https://prove2.me/theorems/de62b18a-6cc5-46cb-9555-8b45ad09f4bf . Identity and proof derived locally; no quoted literature constant or priority claim.

import Mathlib
open scoped BigOperators ComplexConjugate

theorem OddGoldbach19.cosecant_bound_of_cotangent_sharp (C : ℝ)
    (hCot : ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
      (θ δ : κ → ℝ) (v : κ → ℂ),
      (∀ r, 0 < δ r) → (∀ r, δ r ≤ 1) →
      (∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) →
      ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) * ((Real.pi : ℂ) *
          Complex.cot ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))‖ ≤
        C * ∑ r, ‖v r‖ ^ 2 / δ r)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) * ((Real.pi : ℂ) *
        (Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ)))⁻¹)‖ ≤
      C * ∑ r, ‖v r‖ ^ 2 / δ r := by sorry
