-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_orbitSum_mem
-- name    : GroundTheory.Automorphic.GL2Classical.orbitSum_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:02.411815+00:00
-- url     : https://prove2.me/theorems/9ce56267-46ec-4fba-90e7-4778651cc565
-- title:
--   GL2 Classical: orbit Sum mem
-- statement:
--   The GL2 Classical construction uses the orbit Sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/UnitaryEigenSpan.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/UnitaryEigenSpan.lean#L23-L28

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

theorem GroundTheory.Automorphic.GL2Classical.orbitSum_mem {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    {Y : Submodule ℂ E} (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hvY : v ∈ Y) : orbitSum ρ K v hv ∈ Y := by sorry
