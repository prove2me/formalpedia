-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_liftAb_toAb
-- name    : GlobalTheory.HeckeGal.liftAb_toAb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:33.912775+00:00
-- url     : https://prove2.me/theorems/2745df74-c430-4a25-b5eb-3e26a51ae6e3
-- title:
--   Hecke Gal: lift Ab to Ab
-- statement:
--   The Hecke Gal construction uses the lift Ab to Ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L326-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L326-L327

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
omit [NumberField E]

theorem GlobalTheory.HeckeGal.liftAb_toAb {B : Type} [CommGroup B] [TopologicalSpace B] [T1Space B] (φ : G E Ω →* B) (hφ : Continuous φ)
    (σ : G E Ω) : liftAb φ hφ (toAb E Ω σ) = φ σ := by sorry
