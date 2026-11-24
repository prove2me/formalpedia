-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_secPull_surjective_and_ker
-- name    : GlobalTheory.CechDR.secPull_surjective_and_ker
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:35.943166+00:00
-- url     : https://prove2.me/theorems/5c884502-c89e-4609-ab9d-3eb4a94986fc
-- title:
--   Cech DR: sec Pull surjective and ker
-- statement:
--   The Cech DR construction uses the sec Pull surjective and ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SecPullSurjectiveAndKer.lean#L20-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SecPullSurjectiveAndKer.lean#L20-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullSurjectiveAndKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR

theorem GlobalTheory.CechDR.secPull_surjective_and_ker (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ X : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (hpb : IsPullback i s₀ s (spMap π))
    (p : Pair i) (hp : i ⁻¹ᵁ p.1.2.1 = p.1.1.1) :
    Function.Surjective (secPull s s₀ p) ∧
      ∀ b, secPull s s₀ p b = 0 ↔ b ∈ I.map (algebraMap R (Sec s p.1.2.1)) := by sorry
