-- Prove2me | Theorems.Thm_GlobalTheory_TameQuot_ineKer_le_Ine
-- name    : GlobalTheory.TameQuot.ineKer_le_Ine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:46.794803+00:00
-- url     : https://prove2.me/theorems/a415e4f5-7646-400e-9e9f-32736e851b73
-- title:
--   Tame Quot: ine Ker le Ine
-- statement:
--   The Tame Quot construction uses the ine Ker le Ine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L25-L26

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

theorem GlobalTheory.TameQuot.ineKer_le_Ine (A : ValuationSubring Ω) (l : ℕ) : ineKer F A l ≤ Ine (F := F) A := by sorry
