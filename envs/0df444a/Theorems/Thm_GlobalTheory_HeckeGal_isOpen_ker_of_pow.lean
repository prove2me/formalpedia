-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_isOpen_ker_of_pow
-- name    : GlobalTheory.HeckeGal.isOpen_ker_of_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:36.348726+00:00
-- url     : https://prove2.me/theorems/5c95c50b-9fdf-4ec6-a39d-f08a3b4eaf7b
-- title:
--   Hecke Gal: is Open ker of pow
-- statement:
--   The Hecke Gal construction uses the is Open ker of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L363-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L363-L372

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

theorem GlobalTheory.HeckeGal.isOpen_ker_of_pow {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [T1Space Kˣ]
    (φ : Γ →* Kˣ) (hφ : Continuous φ) {m : ℕ} (hm : 0 < m) (h : ∀ g, φ g ^ m = 1) : IsOpen (φ.ker : Set Γ) := by sorry
