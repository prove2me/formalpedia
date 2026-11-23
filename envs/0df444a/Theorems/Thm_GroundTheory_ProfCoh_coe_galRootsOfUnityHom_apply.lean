-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
-- name    : GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:14.653417+00:00
-- url     : https://prove2.me/theorems/7f5775c2-c21d-4a93-974f-044393eaaa27
-- title:
--   Prof Coh: coe gal Roots Of Unity Hom apply
-- statement:
--   The Prof Coh construction uses the coe gal Roots Of Unity Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/CoeGalRootsOfUnityHomApply.lean#L82-L84

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
universe w u v
variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L]

theorem GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply (n : ℕ) (σ : Gal(L/K)) (ζ : rootsOfUnity n L) :
    (((galRootsOfUnityHom K L n σ ζ : Lˣ)) : L) = σ (ζ : Lˣ) := by sorry

attribute [defeq] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
