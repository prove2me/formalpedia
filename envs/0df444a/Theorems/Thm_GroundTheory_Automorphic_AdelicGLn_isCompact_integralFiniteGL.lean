-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_isCompact_integralFiniteGL
-- name    : GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:52.689867+00:00
-- url     : https://prove2.me/theorems/6fdb221d-30f8-458d-91b9-b1c58ea49a1d
-- title:
--   Adelic GLn: is Compact integral Finite GL
-- statement:
--   The Adelic GLn construction uses the is Compact integral Finite GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L201-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L201-L209

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

theorem GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL :
    IsCompact (integralFiniteGL K n : Set (FiniteAdelicGL K n)) := by sorry
