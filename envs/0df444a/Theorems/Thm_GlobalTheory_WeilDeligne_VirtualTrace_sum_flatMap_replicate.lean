-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_VirtualTrace_sum_flatMap_replicate
-- name    : GlobalTheory.WeilDeligne.VirtualTrace.sum_flatMap_replicate
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:13:21.480726+00:00
-- url     : https://prove2.me/theorems/25320fb1-95d4-5d8a-99f6-72a538e31dbd
-- title:
--   Virtual Trace: sum flat Map replicate
-- statement:
--   The Virtual Trace construction uses the sum flat Map replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultiplicativeVirtualCharacter.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MultiplicativeVirtualCharacter.lean#L73-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultiplicativeVirtualCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.VirtualTrace
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem GlobalTheory.WeilDeligne.VirtualTrace.sum_flatMap_replicate {ι α M : Type} [AddCommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).sum = ∑ i ∈ s, n i • g (x i) := by sorry
