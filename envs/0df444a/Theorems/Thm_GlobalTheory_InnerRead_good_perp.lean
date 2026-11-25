-- Prove2me | Theorems.Thm_GlobalTheory_InnerRead_good_perp
-- name    : GlobalTheory.InnerRead.good_perp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:23.679544+00:00
-- url     : https://prove2.me/theorems/04337bbe-e15a-4025-9625-f368b2af3321
-- title:
--   Inner Read: good perp
-- statement:
--   The Inner Read construction uses the good perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NonGenericDatumLatticeEqPerpQuotientImageTerm.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NonGenericDatumLatticeEqPerpQuotientImageTerm.lean#L45-L49

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
noncomputable section
open GlobalTheory GlobalTheory.InnerRead
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem GlobalTheory.InnerRead.good_perp {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    ∀ v ∈ H.perp X, u v ∈ H.perp X := by sorry
