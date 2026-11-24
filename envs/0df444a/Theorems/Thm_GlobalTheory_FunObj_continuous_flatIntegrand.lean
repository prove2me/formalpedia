-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_continuous_flatIntegrand
-- name    : GlobalTheory.FunObj.continuous_flatIntegrand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:53.648578+00:00
-- url     : https://prove2.me/theorems/df94e599-df09-47f1-be27-4cfefdedfe78
-- title:
--   Fun Obj: continuous flat Integrand
-- statement:
--   The Fun Obj construction uses the continuous flat Integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L88-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompactSupportFlatIntegrand.lean#L88-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}

theorem GlobalTheory.FunObj.continuous_flatIntegrand (hs : 1 ≤ G.s) {ψ : AddChar k Circle} (hψ : Continuous ψ) {ϖ : kˣ} {e : ℕ}
    {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : Continuous (flatIntegrand hs ψ (moved G keep g T) x y) := by sorry
