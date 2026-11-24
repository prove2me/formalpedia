-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_apply_eq_pow_cycMod_val
-- name    : GlobalTheory.CompanionTheory.PTIso.apply_eq_pow_cycMod_val
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:23.431693+00:00
-- url     : https://prove2.me/theorems/8aaa3324-b67c-4163-9a8e-9e5713675452
-- title:
--   PTIso: apply eq pow cyc Mod val
-- statement:
--   The PTIso construction uses the apply eq pow cyc Mod val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RingEquivCyclotomicCharacter.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RingEquivCyclotomicCharacter.lean#L11-L17

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivCyclotomicCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso

theorem GlobalTheory.CompanionTheory.PTIso.apply_eq_pow_cycMod_val {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω) {ζ : Ω} (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycMod F Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by sorry
