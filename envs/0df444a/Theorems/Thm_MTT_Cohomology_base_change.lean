-- Prove2me | Theorems.Thm_MTT_Cohomology_base_change
-- name    : MTT.Cohomology.base_change
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T13:59:43.81372+00:00
-- url     : https://prove2.me/theorems/55e287ab-365f-40fb-a1e3-d7a58f9f4d43
-- title:
--   Flat base change for compactly supported group cohomology
-- statement:
--   For positive level, coefficientwise extension gives the canonical R-linear isomorphism R ⊗_Z Hc¹(Γ₁(N), Symⁿ Z²) ≃ Hc¹(Γ₁(N), Symⁿ R²) for every commutative ring flat over Z. This includes Qbar, C and Cp. Compatibility is specified on pure tensors, not merely existence of an unrelated isomorphism.
-- source:
--   Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §4, Definition 4.1 and Proposition 4.2, pp. 861–863, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf. Integral statements use relative group cohomology, not the coarse quotient at elliptic points. Flat base change is the finite-presentation consequence of this modular-symbol model.

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.base_change
    {N n : ℕ} (hN : 0 < N) (R : Type*) [CommRing R] [Module.Flat ℤ R] :
    BaseChange N n R := by sorry
