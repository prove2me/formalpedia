-- Prove2me | Theorems.Thm_GlobalTheory_TamePairing_eq_zero_of_isProGen
-- name    : GlobalTheory.TamePairing.eq_zero_of_isProGen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:02:13.810855+00:00
-- url     : https://prove2.me/theorems/33372a59-9d73-45df-8d4a-bc0803625740
-- title:
--   Tame Pairing: eq zero of is Pro Gen
-- statement:
--   The Tame Pairing construction uses the eq zero of is Pro Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TamePairing.lean#L12-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TamePairing.lean#L12-L50

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TamePairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.TamePairing
open GlobalTheory.TameQuot

theorem GlobalTheory.TamePairing.eq_zero_of_isProGen {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {l : ℕ} [hl : Fact l.Prime] {n : ℕ} {A : ValuationSubring Ω} {γ₀ : Dec (F := F) A}
    (hγ : IsProGen F A l (γ₀ : G F Ω)) (f : Dec (F := F) A → ZMod (l ^ n)) (hf : Continuous f)
    (hadd : ∀ g h, f (g * h) = f g + f h) (h0 : f γ₀ = 0) (σ : Dec (F := F) A)
    (hσ : (σ : G F Ω) ∈ Ine (F := F) A) : f σ = 0 := by sorry
