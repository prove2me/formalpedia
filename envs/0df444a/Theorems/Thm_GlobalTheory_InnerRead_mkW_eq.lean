-- Prove2me | Theorems.Thm_GlobalTheory_InnerRead_mkW_eq
-- name    : GlobalTheory.InnerRead.mkW_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:16:04.654807+00:00
-- url     : https://prove2.me/theorems/4201a837-fbba-4387-b5bc-7befcceb53f7
-- title:
--   Inner Read: mk W eq
-- statement:
--   The Inner Read construction uses the mk W eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NonGenericDatumLatticeEqPerpQuotientImageTerm.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NonGenericDatumLatticeEqPerpQuotientImageTerm.lean#L30-L34

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

theorem GlobalTheory.InnerRead.mkW_eq {r : ℕ} {f : Fin (r + 1) → V} (x y : ↥(H.perp (H.X f))) (h : (x : V) - y ∈ H.X f) :
    H.mkW f x = H.mkW f y := by sorry
