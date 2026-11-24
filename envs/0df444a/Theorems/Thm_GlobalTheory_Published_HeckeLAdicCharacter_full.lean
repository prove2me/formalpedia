-- Prove2me | Theorems.Thm_GlobalTheory_Published_HeckeLAdicCharacter_full
-- name    : GlobalTheory.Published.HeckeLAdicCharacter.full
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:49.31359+00:00
-- url     : https://prove2.me/theorems/1692ac6c-d6ef-4b4d-a973-266a0df9817e
-- title:
--   Hecke LAdic Character: full
-- statement:
--   The Hecke LAdic Character construction uses the full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L466-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L466-L491

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.Published
open GlobalTheory.HeckeGal

theorem GlobalTheory.Published.HeckeLAdicCharacter.full (H : HeckeLAdicCharacter) (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] :
    ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧ ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
      (∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), χ.IsAlg n →
        ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r ∧
          (∀ r', IsLAdicOf art ι χ n r' → r' = r) ∧
          ∀ v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
            (∀ z : Qbar l, (∃ σ ∈ Ine (F := E) A, ((r σ : (Qbar l)ˣ) : Qbar l) = z) ↔
              ∃ x, IsUnitAt v x ∧ ι.symm ((χ.loc v x : ℂˣ) : ℂ) = z) ∧
            ((∀ σ ∈ Ine (F := E) A, r σ = 1) ↔ χ.UnrAt v) ∧
            (χ.UnrAt v → ∀ σ : G E Ω, IsFrob (F := E) A (normV v) σ →
              ((r σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val v : ℂˣ) : ℂ))⁻¹)) ∧
      (∀ m : ℕ, 0 < m → ∀ χ : HChar E, χ.OrderDvd m →
        ∃! r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ r ^ m = 1 ∧ IsLAdicOf art ι χ 0 r) ∧
      (∀ m : ℕ, 0 < m → ∀ r : G E Ω →* (Qbar l)ˣ, Continuous r → r ^ m = 1 →
        ∃! χ : HChar E, χ.OrderDvd m ∧ IsLAdicOf art ι χ 0 r) := by sorry
