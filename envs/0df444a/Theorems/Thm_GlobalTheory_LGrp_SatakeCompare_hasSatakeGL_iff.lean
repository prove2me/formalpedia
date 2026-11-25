-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_SatakeCompare_hasSatakeGL_iff
-- name    : GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:16.624174+00:00
-- url     : https://prove2.me/theorems/f828f4e7-fc78-4e30-9e1f-9a32d49e64b8
-- title:
--   Satake Compare: has Satake GL iff
-- statement:
--   The Satake Compare construction uses the has Satake GL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSubquotSmIndCongr.lean#L178-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSubquotSmIndCongr.lean#L178-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSubquotSmIndCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel
open scoped NNReal
open GlobalTheory GlobalTheory.LGrp GlobalTheory.LGrp.SatakeCompare
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
open MeasureTheory ValuativeRel
open scoped NNReal
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

theorem GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n V : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (S : Multiset ℂˣ), _root_.GlobalTheory.LGrp.HasSatakeGL π S ↔
      ∃ α : n → ℂˣ, Finset.univ.val.map α = S ∧ _root_.GlobalTheory.SmGL.HasSatake π α := by sorry
