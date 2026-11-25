-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_exists_basicOpen_of_isSncModel
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_basicOpen_of_isSncModel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:20:06.069125+00:00
-- url     : https://prove2.me/theorems/2333fc1e-9266-4610-ad5f-e036c1fa7bf3
-- title:
--   Par: exists basic Open of is Snc Model
-- statement:
--   The Par construction uses the exists basic Open of is Snc Model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ExistsBasicOpenOfIsSncModel.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ExistsBasicOpenOfIsSncModel.lean#L11-L30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsBasicOpenOfIsSncModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_basicOpen_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)), IsSncModel y e J → ∀ p : (k : K) → ι k, (∀ k, y ⟨k, p k⟩ ≠ 0) → ∀ t : (Σ k, ι k) → ℂ, (∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → ∃ (F : MvPolynomial (Σ k, ι k) ℚ) (S : Subalgebra ℚ Ω) (z : Fin e → S) (n : ℕ), aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F ≠ 0 ∧ eval t (map (algebraMap ℚ ℂ) F) ≠ 0 ∧ S = Algebra.adjoin ℚ (insert (aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F)⁻¹ (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩))) ∧ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧ ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by sorry
