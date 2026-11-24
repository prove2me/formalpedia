-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_hermA_tmul_fv
-- name    : GlobalTheory.AdLat.hermA_tmul_fv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:21:13.242846+00:00
-- url     : https://prove2.me/theorems/b3d53638-6d1f-4ab9-9175-9f9b2ea0f2e6
-- title:
--   Ad Lat: herm A tmul fv
-- statement:
--   The Ad Lat construction uses the herm A tmul fv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionSelfDualOfSelfDualLattice.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionSelfDualOfSelfDualLattice.lean#L21-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat

theorem GlobalTheory.AdLat.hermA_tmul_fv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (t : FiniteAdeleRing (𝓞 F) F) (x y : Fin n → E) :
    hermA c G (fun i => t ⊗ₜ[F] x i) (fv F y) = t ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) := by sorry
