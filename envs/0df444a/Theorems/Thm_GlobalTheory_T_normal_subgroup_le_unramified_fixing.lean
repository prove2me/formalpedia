-- Prove2me | Theorems.Thm_GlobalTheory_T_normal_subgroup_le_unramified_fixing
-- name    : GlobalTheory.T.normal_subgroup_le_unramified_fixing
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:38:01.564593+00:00
-- url     : https://prove2.me/theorems/0d2a9258-f8a1-4e11-a431-9b1a96fc711f
-- title:
--   T: normal subgroup le unramified fixing
-- statement:
--   The T construction uses the normal subgroup le unramified fixing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NormalSubgroupLeUnramifiedFixingStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NormalSubgroupLeUnramifiedFixingStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixing
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.normal_subgroup_le_unramified_fixing : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), NS Ω S ≤ (maxUnramifiedOutside F Ω S).fixingSubgroup := by sorry
