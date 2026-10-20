-- Prove2me | Theorems.Thm_MetricCodes_projection_certificate_mul
-- name    : MetricCodes.projection_certificate_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/8c491a94-a62f-4f07-81ab-4a2ec649e930
-- title:
--   MetricCodes.projection_certificate_mul
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D d : ℕ}

theorem MetricCodes.projection_certificate_mul
    (P : ProjectionFamily X D d)
    (C : Finset X)
    (t : X → X → ℝ)
    (q : X → E)
    {s lam : ℝ}
    (hd : 0 < d)
    (hs : s < 1)
    (hgap : s < lam)
    (hdiag : ∀ x ∈ C, t x x = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → t x y ≤ s)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ = (t x y - lam) * P.overlap x y) :
    (C.card : ℝ) * (lam - s) * (d : ℝ) ≤
      (1 - s) * (D : ℝ) := by sorry
