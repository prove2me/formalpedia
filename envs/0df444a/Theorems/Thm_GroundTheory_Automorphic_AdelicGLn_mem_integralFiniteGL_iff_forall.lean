-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_mem_integralFiniteGL_iff_forall
-- name    : GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff_forall
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:12.055416+00:00
-- url     : https://prove2.me/theorems/d79e3610-0012-483b-b694-ab0657c9c164
-- title:
--   Adelic GLn: mem integral Finite GL iff forall
-- statement:
--   The Adelic GLn construction uses the mem integral Finite GL iff forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L158-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L158-L172

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

theorem GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff_forall {g : FiniteAdelicGL K n} :
    g ∈ integralFiniteGL K n ↔
      ∀ v, finiteRestrictedEquiv K n g v ∈ GLnLocal.integralGL (v.adicCompletion K) n := by sorry
