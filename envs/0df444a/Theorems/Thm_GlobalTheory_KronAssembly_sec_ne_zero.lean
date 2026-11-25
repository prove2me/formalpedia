-- Prove2me | Theorems.Thm_GlobalTheory_KronAssembly_sec_ne_zero
-- name    : GlobalTheory.KronAssembly.sec_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:00:54.548408+00:00
-- url     : https://prove2.me/theorems/08b9b793-20cd-4dde-bc53-0a31747c2e7b
-- title:
--   Kron Assembly: sec ne zero
-- statement:
--   The Kron Assembly construction uses the sec ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/KronHolPsiOf.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/KronHolPsiOf.lean#L31-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_KronHolPsiOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.KronAssembly
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.KronAssembly.sec_ne_zero {r : ℕ} (X : Data E r) {L : Wt X.Ψ r} {w : Frame X.Ψ r → ℂ} (hw : X.IsSec L w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (h : w x ≠ 0) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : w (lact γ (rmul x b)) ≠ 0 := by sorry
