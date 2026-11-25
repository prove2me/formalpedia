-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_sum_local_trace
-- name    : GlobalTheory.ResidueCharacterDense.sum_local_trace
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:48.354392+00:00
-- url     : https://prove2.me/theorems/c9296e81-fbb6-4887-9dff-ecf5231f42ff
-- title:
--   Residue Character Dense: sum local trace
-- statement:
--   The Residue Character Dense construction uses the sum local trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L276-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L276-L314

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

theorem GlobalTheory.ResidueCharacterDense.sum_local_trace {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F]
    {S : Type} [Fintype S] (P : S → HeightOneSpectrum (𝓞 F)) (hP : Function.Injective P)
    (hS : ∀ I : Ideal (𝓞 F), I.IsPrime → (l : 𝓞 F) ∈ I → ∃ s, (P s).asIdeal = I)
    (K : S → Type) [∀ s, Field (K s)] [∀ s, TopologicalSpace (K s)]
    [∀ s, IsTopologicalRing (K s)] [∀ s, T2Space (K s)] [∀ s, CharZero (K s)]
    [∀ s, Algebra ℚ_[l] (K s)] [∀ s, FiniteDimensional ℚ_[l] (K s)]
    [∀ s, ContinuousSMul ℚ_[l] (K s)] (ι : ∀ s, F →+* K s) (U : ∀ s, Set (K s))
    (hd : ∀ s, DenseRange (ι s)) (hUo : ∀ s, IsOpen (U s))
    (hU : ∀ s x, ι s x ∈ U s ↔ (P s).valuation F x < 1)
    (hpow : ∀ s, ∀ z ∈ U s, Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0)) (t : F) :
    ∑ s, Algebra.trace ℚ_[l] (K s) (ι s t) = ((Algebra.trace ℚ F t : ℚ) : ℚ_[l]) := by sorry
