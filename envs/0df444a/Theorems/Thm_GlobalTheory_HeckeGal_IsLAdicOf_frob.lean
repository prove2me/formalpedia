-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_frob
-- name    : GlobalTheory.HeckeGal.IsLAdicOf.frob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:54.197776+00:00
-- url     : https://prove2.me/theorems/4c7ee154-9719-4df5-a9d4-dbb82687f869
-- title:
--   Is LAdic Of: frob
-- statement:
--   The Is LAdic Of construction uses the frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L288-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L288-L294

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
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
variable {art : Ideles E →* Gab E Ω} {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ}
  {r : G E Ω →* (Qbar l)ˣ} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem GlobalTheory.HeckeGal.IsLAdicOf.frob (ha : IsGlobalArtin art) (h : IsLAdicOf art ι χ n r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) :
    ∃ x, IsUnifAt v x ∧ ((r σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.loc v x : ℂˣ) : ℂ))⁻¹ := by sorry
