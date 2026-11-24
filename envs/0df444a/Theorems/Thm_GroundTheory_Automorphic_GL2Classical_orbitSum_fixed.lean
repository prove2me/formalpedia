-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_orbitSum_fixed
-- name    : GroundTheory.Automorphic.GL2Classical.orbitSum_fixed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:50.878801+00:00
-- url     : https://prove2.me/theorems/493e8409-a3cc-4221-a028-3096e559755b
-- title:
--   GL2 Classical: orbit Sum fixed
-- statement:
--   The GL2 Classical construction uses the orbit Sum fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/UnitaryEigenSpan.lean#L30-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/UnitaryEigenSpan.lean#L30-L48

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_UnitaryEigenSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)
variable {ρ}

theorem GroundTheory.Automorphic.GL2Classical.orbitSum_fixed {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    (k : K) : ρ k (orbitSum ρ K v hv) = orbitSum ρ K v hv := by sorry
