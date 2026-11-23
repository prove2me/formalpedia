-- Prove2me | Theorems.Thm_GlobalTheory_TameQuot_coe_mem_ineKer
-- name    : GlobalTheory.TameQuot.coe_mem_ineKer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:05.854966+00:00
-- url     : https://prove2.me/theorems/965368cd-5564-4659-89ac-4dc055518b16
-- title:
--   Tame Quot: coe mem ine Ker
-- statement:
--   The Tame Quot construction uses the coe mem ine Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L28-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.TameQuot
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem GlobalTheory.TameQuot.coe_mem_ineKer {A : ValuationSubring Ω} {l : ℕ} {σ : Ine (F := F) A} :
    (σ : G F Ω) ∈ ineKer F A l ↔ σ ∈ proKer l (Ine (F := F) A) := by sorry
