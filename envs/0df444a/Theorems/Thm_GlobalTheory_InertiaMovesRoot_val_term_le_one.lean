-- Prove2me | Theorems.Thm_GlobalTheory_InertiaMovesRoot_val_term_le_one
-- name    : GlobalTheory.InertiaMovesRoot.val_term_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:58:56.104528+00:00
-- url     : https://prove2.me/theorems/482ba94e-366f-576d-bee5-7d4ea4c374fc
-- title:
--   Inertia Moves Root: val term le one
-- statement:
--   The Inertia Moves Root construction uses the val term le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L48-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
open GlobalTheory GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem GlobalTheory.InertiaMovesRoot.val_term_le_one {ι : Type*} (s : Finset ι) (f : ι → Ω)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → A.valuation (f i) = A.valuation (f j) → i = j)
    (hs : A.valuation (∑ i ∈ s, f i) ≤ 1) : ∀ i ∈ s, A.valuation (f i) ≤ 1 := by sorry
