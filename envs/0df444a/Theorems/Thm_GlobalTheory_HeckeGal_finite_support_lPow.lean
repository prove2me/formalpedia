-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_finite_support_lPow
-- name    : GlobalTheory.HeckeGal.finite_support_lPow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:05.783807+00:00
-- url     : https://prove2.me/theorems/ed03dee4-8cca-4bab-970c-e3ccab4085ae
-- title:
--   Hecke Gal: finite support l Pow
-- statement:
--   The Hecke Gal construction uses the finite support l Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L153-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L153-L163

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

theorem GlobalTheory.HeckeGal.finite_support_lPow (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (x : Ideles E) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
      locPow ι n v ((x : AdeleRing (𝓞 E) E).2 v)).Finite := by sorry
