-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_eventually_mem_integralGL
-- name    : GroundTheory.Automorphic.AdelicGLn.eventually_mem_integralGL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:45.637977+00:00
-- url     : https://prove2.me/theorems/6d31da50-ba71-4f67-b47e-fcf3f198f6cc
-- title:
--   Adelic GLn: eventually mem integral GL
-- statement:
--   The Adelic GLn construction uses the eventually mem integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L131-L134

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.AdelicGLn
variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

theorem GroundTheory.Automorphic.AdelicGLn.eventually_mem_integralGL (g : AdelicGL K n) :
    ∀ᶠ v in cofinite, (restrictedProductEquiv K n g).2 v ∈
      GLnLocal.integralGL (v.adicCompletion K) n := by sorry
