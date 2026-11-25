-- Prove2me | Theorems.Thm_GlobalTheory_Nef_PathJet_exists_jet_succ_of_lift
-- name    : GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:49.090249+00:00
-- url     : https://prove2.me/theorems/196fe6cf-4c65-4d7c-b311-325ad8524a82
-- title:
--   Path Jet: exists jet succ of lift
-- statement:
--   The Path Jet construction uses the exists jet succ of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDoublingJetSuccOfLift.lean#L34-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDoublingJetSuccOfLift.lean#L34-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDoublingJetSuccOfLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PathJet
open PowerSeries

theorem GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R]
    (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π) (hεm : ε.comp m = ε)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (_hδ : ∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) (_hδπ : ∀ a, δ (π a) = 0)
    (n : ℕ) (hn : 2 ≤ n) (φ ψ : A → PowerSeries R) (hφ : IsJet π ε m β δ n φ)
    (hψ : IsRingHomMod π β (n + 1) ψ) (hψφ : ∀ f, (X : PowerSeries R) ^ n ∣ ψ f - φ f) :
    ∃ ψ' : A → PowerSeries R, IsJet π ε m β δ (n + 1) ψ' ∧
      ∀ f, (X : PowerSeries R) ^ n ∣ ψ' f - φ f := by sorry
