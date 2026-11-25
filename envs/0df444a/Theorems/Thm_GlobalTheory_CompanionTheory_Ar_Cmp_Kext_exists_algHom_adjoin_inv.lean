-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_Kext_exists_algHom_adjoin_inv
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.Kext.exists_algHom_adjoin_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:19:45.745006+00:00
-- url     : https://prove2.me/theorems/04e2c1b0-03e8-4530-9ade-39c734b5efeb
-- title:
--   Kext: exists alg Hom adjoin inv
-- statement:
--   The Kext construction uses the exists alg Hom adjoin inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ExistsAlgHomAdjoinInv.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ExistsAlgHomAdjoinInv.lean#L9-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsRestAlt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.Kext

theorem GlobalTheory.CompanionTheory.Ar.Cmp.Kext.exists_algHom_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω) (E : Type) [CommRing E] [Algebra ℚ E] (u : σ → E),
      aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → aeval u G = 0) → IsUnit (aeval u F) →
      ∃ φ : S →ₐ[ℚ] E, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval τ G →
        φ s = aeval u G := by sorry
