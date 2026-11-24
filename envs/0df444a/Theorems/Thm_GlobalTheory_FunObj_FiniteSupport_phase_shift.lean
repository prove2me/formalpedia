-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_phase_shift
-- name    : GlobalTheory.FunObj.FiniteSupport.phase_shift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:43:27.113043+00:00
-- url     : https://prove2.me/theorems/04e9b453-9b89-4f55-9e82-58ba7cae4e64
-- title:
--   Finite Support: phase shift
-- statement:
--   The Finite Support construction uses the phase shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L166-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L166-L181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {G : Grid k} (hs : 1 ≤ G.s)

theorem GlobalTheory.FunObj.FiniteSupport.phase_shift {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (x : ColArgs G) (e : Vars G) :
    phase x (shiftVars d + e) = phase x e + ∑ j, ch (d j) := by sorry
