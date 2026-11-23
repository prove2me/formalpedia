-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_borel_inf_integralGL_iff
-- name    : GroundTheory.Automorphic.Iwasawa.mem_borel_inf_integralGL_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:31.609502+00:00
-- url     : https://prove2.me/theorems/ee78f78d-1fb9-42b3-ba06-6e3c0ce0ce76
-- title:
--   Iwasawa: mem borel inf integral GL iff
-- statement:
--   The Iwasawa construction uses the mem borel inf integral GL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L134-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L134-L158

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F]

theorem GroundTheory.Automorphic.Iwasawa.mem_borel_inf_integralGL_iff {g : GL (Fin n) F} :
    g ∈ borel F n ⊓ integralGL F n ↔
      g ∈ borel F n ∧ (∀ i j, g i j ∈ 𝒪[F]) ∧ ∀ i, valuation F (g i i) = 1 := by sorry
