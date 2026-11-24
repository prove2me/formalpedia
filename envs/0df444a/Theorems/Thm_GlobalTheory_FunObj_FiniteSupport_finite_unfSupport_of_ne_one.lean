-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_finite_unfSupport_of_ne_one
-- name    : GlobalTheory.FunObj.FiniteSupport.finite_unfSupport_of_ne_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:43:33.939531+00:00
-- url     : https://prove2.me/theorems/6abe40a4-f382-4f44-bf68-d95b17c71d13
-- title:
--   Finite Support: finite unf Support of ne one
-- statement:
--   The Finite Support construction uses the finite unf Support of ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L375-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L375-L409

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] {G : Grid k} {hs : 1 ≤ G.s} {ψ : AddChar k Circle} (ν : Measure k)
  [ν.IsAddHaarMeasure]

theorem GlobalTheory.FunObj.FiniteSupport.finite_unfSupport_of_ne_one (hψ : ψ ≠ 1) {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) {J : G.Level}
    (hJ : ∀ j, 0 < j → j < G.m → IsOpen (J (G.m, j) : Set (GL (Fin (G.rank (G.m, j))) k)))
    (keep : Bool) (ρ : Reps hs J) : (unfSupport ψ ν keep ρ T).Finite := by sorry
