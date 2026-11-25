-- Prove2me | Theorems.Thm_GlobalTheory_HL_LatCard_relIndex_map_of_param
-- name    : GlobalTheory.HL.LatCard.relIndex_map_of_param
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:31:44.859956+00:00
-- url     : https://prove2.me/theorems/f579480c-cffe-49fe-88c8-e1ca0661149f
-- title:
--   Lat Card: rel Index map of param
-- statement:
--   The Lat Card construction uses the rel Index map of param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexTupleLatticeHermitianLatticeUniformizer.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexTupleLatticeHermitianLatticeUniformizer.lean#L14-L24

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatCard

theorem GlobalTheory.HL.LatCard.relIndex_map_of_param {G W : Type*} [AddCommGroup G] [AddCommGroup W] (f : G →+ W)
    (hf : Function.Injective f) (A : AddSubgroup W) (hA : ∀ w, w ∈ A ↔ ∃ g, f g = w)
    (T : W →+ W) (t : G → G) (ht : ∀ g, f (t g) = T (f g)) (H : AddSubgroup G)
    (hH : ∀ g, g ∈ H ↔ ∃ g', t g' = g) : (A.map T).relIndex A = H.index := by sorry
