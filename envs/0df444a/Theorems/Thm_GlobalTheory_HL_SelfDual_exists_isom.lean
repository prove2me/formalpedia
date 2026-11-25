-- Prove2me | Theorems.Thm_GlobalTheory_HL_SelfDual_exists_isom
-- name    : GlobalTheory.HL.SelfDual.exists_isom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:46.626942+00:00
-- url     : https://prove2.me/theorems/75fe105e-d74f-4dbf-bd19-324198911e04
-- title:
--   Self Dual: exists isom
-- statement:
--   The Self Dual construction uses the exists isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrthonormalBasisAndOneOrbit.lean#L165-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrthonormalBasisAndOneOrbit.lean#L165-L186

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SelfDual
open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.SelfDual.exists_isom (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    {b b' : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤)
    (hb' : Submodule.span E (Set.range b') = ⊤)
    (ho : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0)
    (ho' : ∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) :
    ∃ g ∈ isomG L Hm, ∀ i, g (b i) = b' i := by sorry
