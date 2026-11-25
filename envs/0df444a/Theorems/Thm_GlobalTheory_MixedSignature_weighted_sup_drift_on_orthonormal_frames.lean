-- Prove2me | Theorems.Thm_GlobalTheory_MixedSignature_weighted_sup_drift_on_orthonormal_frames
-- name    : GlobalTheory.MixedSignature.weighted_sup_drift_on_orthonormal_frames
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:13:52.520936+00:00
-- url     : https://prove2.me/theorems/c5e56065-34e0-47d3-9ab9-e72241f98de7
-- title:
--   Mixed Signature: weighted sup drift on orthonormal frames
-- statement:
--   The Mixed Signature construction uses the weighted sup drift on orthonormal frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeightedSupDriftOnOrthonormalFrames.lean#L199-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeightedSupDriftOnOrthonormalFrames.lean#L199-L248

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
import Theorems.Thm_GlobalTheory_FiniteCovolume_weighted_sup_drift_on_orthonormal_frames
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

theorem GlobalTheory.MixedSignature.weighted_sup_drift_on_orthonormal_frames :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1)) → ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∃ (e : ℕ → ℝ) (c b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ ∀ x, Orth X G p x → ∑ a ∈ S, (∑ i ∈ Finset.Ioo 0 r, e i * α i (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) ≤ S.card * (c * (∑ i ∈ Finset.Ioo 0 r, e i * α i x) + b)) := by sorry
