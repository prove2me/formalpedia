-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mem_nPlusU
-- name    : GroundTheory.Automorphic.HarishChandra.canon_mem_nPlusU
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:07:21.285417+00:00
-- url     : https://prove2.me/theorems/5813abe1-6c02-4ccc-a139-682c3d00d461
-- title:
--   Harish Chandra: canon mem n Plus U
-- statement:
--   The Harish Chandra construction uses the canon mem n Plus U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L215-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L215-L220

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
open scoped IsMulCommutative

theorem GroundTheory.Automorphic.HarishChandra.canon_mem_nPlusU {m : Fin n × Fin n →₀ ℕ} (h : HasUpper m) : canon m ∈ nPlusU n := by sorry
