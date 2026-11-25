-- Prove2me | Theorems.Thm_GlobalTheory_Reg_IdemCusp_mul_mem_holSub
-- name    : GlobalTheory.Reg.IdemCusp.mul_mem_holSub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:18:58.607308+00:00
-- url     : https://prove2.me/theorems/05c67e97-b4ff-4169-b042-35fe57673a43
-- title:
--   Idem Cusp: mul mem hol Sub
-- statement:
--   The Idem Cusp construction uses the mul mem hol Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IdemMulMemCusp.lean#L98-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IdemMulMemCusp.lean#L98-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IdemMulMemCusp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.IdemCusp
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Reg.IdemCusp.mul_mem_holSub {ι : Type} (X : ι → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    (χ : Formalism.L2.PjFree.FDSec X) (hχ : ∀ k, IsIdemFn (X k) (χ k)) {P : Formalism.L2.PjFree.FDSec X}
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) : (fun k => χ k * P k) ∈ Formalism.L2.PjFree.holSub X la := by sorry
