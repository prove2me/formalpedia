-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_smallIdeal_comp
-- name    : GlobalTheory.ResidueCharacterDense.smallIdeal_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:24.828474+00:00
-- url     : https://prove2.me/theorems/68c944de-dc31-4f37-b690-14746bc1a747
-- title:
--   Residue Character Dense: small Ideal comp
-- statement:
--   The Residue Character Dense construction uses the small Ideal comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L175-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L175-L188

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
omit [CharZero K]

theorem GlobalTheory.ResidueCharacterDense.smallIdeal_comp (hU : ∀ x, ι x ∈ U ↔ p.valuation F x < 1)
    (hpow : ∀ z ∈ U, Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0))
    (τ : K →ₐ[ℚ_[l]] PadicAlgCl l) :
    p.asIdeal = smallIdeal ((τ : K →+* PadicAlgCl l).comp ι) := by sorry
