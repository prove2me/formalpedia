-- Prove2me | Theorems.Thm_GlobalTheory_TameQuot_mem_proKer
-- name    : GlobalTheory.TameQuot.mem_proKer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:59.434804+00:00
-- url     : https://prove2.me/theorems/c1c68bf4-2cf2-4b79-8819-bba1df62a118
-- title:
--   Tame Quot: mem pro Ker
-- statement:
--   The Tame Quot construction uses the mem pro Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L13-L16

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

theorem GlobalTheory.TameQuot.mem_proKer {l : ℕ} {H : Type*} [Group H] [TopologicalSpace H] {x : H} :
    x ∈ proKer l H ↔
      ∀ U : Subgroup H, U.Normal → IsOpen (U : Set H) → (∃ n : ℕ, U.index = l ^ n) → x ∈ U := by sorry
