-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_PlaneRefl_hf_add_right
-- name    : GlobalTheory.UTrans.PlaneRefl.hf_add_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:29.776803+00:00
-- url     : https://prove2.me/theorems/5263fff6-037c-4be7-bef2-35fd70bf6336
-- title:
--   Plane Refl: hf add right
-- statement:
--   The Plane Refl construction uses the hf add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqMulTransvectionsOfHyperbolicPla.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqMulTransvectionsOfHyperbolicPla.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpecialUnitaryHyperbolicPlaneMemTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPla
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_add_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.PlaneRefl
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem GlobalTheory.UTrans.PlaneRefl.hf_add_right (x y v : Fin n → R) : hf σ G v (x + y) = hf σ G v x + hf σ G v y := by sorry
