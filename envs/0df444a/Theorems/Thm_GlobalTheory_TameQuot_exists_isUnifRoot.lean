-- Prove2me | Theorems.Thm_GlobalTheory_TameQuot_exists_isUnifRoot
-- name    : GlobalTheory.TameQuot.exists_isUnifRoot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:12.755798+00:00
-- url     : https://prove2.me/theorems/4aa1130c-a70f-4143-9f08-8470863d7a9c
-- title:
--   Tame Quot: exists is Unif Root
-- statement:
--   The Tame Quot construction uses the exists is Unif Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L94-L100

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

theorem GlobalTheory.TameQuot.exists_isUnifRoot [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : 0 < N) :
    ∃ x : Ω, IsUnifRoot v N x := by sorry
