-- Prove2me | Theorems.Thm_GlobalTheory_MixedSignature_minGe_of_lines
-- name    : GlobalTheory.MixedSignature.minGe_of_lines
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:10:16.054727+00:00
-- url     : https://prove2.me/theorems/13b17fce-8a47-4567-81d7-bfb1871ed8a2
-- title:
--   Mixed Signature: min Ge of lines
-- statement:
--   The Mixed Signature construction uses the min Ge of lines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeightedSupDriftOnOrthonormalFrames.lean#L165-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeightedSupDriftOnOrthonormalFrames.lean#L165-L197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_OrthonormalFramesBoundedOfDefinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightBotTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumLowerOfLineHeights
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSubspaceHeightGramDeterminant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteMeasureCoverOfDriftFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetReNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIsLUBHeightRpowLowerSemicontinuousOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightRpowNegDistortionContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_WeightedHeightSupDriftOrthonormalFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionOrthonormalHermitianFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionRealUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeightedSupDriftOnOrthonormalFrames
import Theorems.Thm_GlobalTheory_DriftUnitary_continuous_orbit
import Theorems.Thm_GlobalTheory_FiniteCovolume_nonneg_of_isLUB_image
import Theorems.Thm_GlobalTheory_HeightEnds_gramDet_square
import Theorems.Thm_GlobalTheory_HeightInv_relIndex_span_map
import Theorems.Thm_GlobalTheory_LineHeight_c_pos
import Theorems.Thm_GlobalTheory_LineHeight_exists_min_le_of_le_prod
import Theorems.Thm_GlobalTheory_LineHeight_gramDet_column
import Theorems.Thm_GlobalTheory_LineHeight_nonempty_cmType
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_c_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.MixedSignature
open GlobalTheory.HeightInv (relIndex_span_map)
open GlobalTheory.HeightEnds (gramDet_square)
open GlobalTheory.LineHeight (gramDet_column exists_min_le_of_le_prod nonempty_cmType c_pos)
open GlobalTheory.FiniteCovolume (nonneg_of_isLUB_image)
open GlobalTheory.DriftUnitary (continuous_orbit)
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.MixedSignature.minGe_of_lines : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → MinGe X ε x) := by sorry
