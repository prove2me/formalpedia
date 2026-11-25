-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_algHom_ext_dense
-- name    : GlobalTheory.ResidueCharacterDense.algHom_ext_dense
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:09.452053+00:00
-- url     : https://prove2.me/theorems/2a09590f-841b-5d58-b005-fd1c4c522c52
-- title:
--   Residue Character Dense: alg Hom ext dense
-- statement:
--   The Residue Character Dense construction uses the alg Hom ext dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L168-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L168-L172

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
variable {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F]
  (p : HeightOneSpectrum (𝓞 F)) {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] [CharZero K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K] [ContinuousSMul ℚ_[l] K]
  (ι : F →+* K) (U : Set K)
omit [NumberField F] [CharZero K]

theorem GlobalTheory.ResidueCharacterDense.algHom_ext_dense (hd : DenseRange ι) (τ τ' : K →ₐ[ℚ_[l]] PadicAlgCl l)
    (h : ∀ x, τ (ι x) = τ' (ι x)) : τ = τ' := by sorry
