-- Prove2me | Theorems.Thm_GlobalTheory_InnerRead_good_of_mem_N
-- name    : GlobalTheory.InnerRead.good_of_mem_N
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:39:29.208228+00:00
-- url     : https://prove2.me/theorems/c4a735a9-4980-49cd-a89e-af3f4f016251
-- title:
--   Inner Read: good of mem N
-- statement:
--   The Inner Read construction uses the good of mem N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NonGenericDatumLatticeEqPerpQuotientImageTerm.lean#L193-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NonGenericDatumLatticeEqPerpQuotientImageTerm.lean#L193-L200

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
variable {H} {r : ℕ} (Fr : FrameD H r)

theorem GlobalTheory.InnerRead.good_of_mem_N {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : Good H (H.X Fr.f) g := by sorry
