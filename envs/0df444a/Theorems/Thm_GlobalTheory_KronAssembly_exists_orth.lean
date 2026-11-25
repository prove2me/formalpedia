-- Prove2me | Theorems.Thm_GlobalTheory_KronAssembly_exists_orth
-- name    : GlobalTheory.KronAssembly.exists_orth
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:49:19.396646+00:00
-- url     : https://prove2.me/theorems/a660652b-a6cd-44f8-8a6f-1b9124f9eb82
-- title:
--   Kron Assembly: exists orth
-- statement:
--   The Kron Assembly construction uses the exists orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/KronHolPsiOf.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/KronHolPsiOf.lean#L24-L29

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

theorem GlobalTheory.KronAssembly.exists_orth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) : ∃ x1, IsOrth X x1 ∧ ∃ b ∈ Bor X.Ψ r, ∃ b' ∈ Bor X.Ψ r,
      lact γ x = rmul x1 b ∧ x1 = lact γ (rmul x b') := by sorry
