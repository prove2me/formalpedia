-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_isClosed_rationalGL
-- name    : GroundTheory.Automorphic.AdelicGLn.isClosed_rationalGL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:04:42.881912+00:00
-- url     : https://prove2.me/theorems/fda05602-997f-4441-b541-0053c956909d
-- title:
--   Adelic GLn: is Closed rational GL
-- statement:
--   The Adelic GLn construction uses the is Closed rational GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L296-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L296-L298

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

theorem GroundTheory.Automorphic.AdelicGLn.isClosed_rationalGL : IsClosed (rationalGL K n : Set (AdelicGL K n)) := by sorry
