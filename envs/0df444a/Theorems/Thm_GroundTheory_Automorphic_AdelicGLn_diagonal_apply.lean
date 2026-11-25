-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
-- name    : GroundTheory.Automorphic.AdelicGLn.diagonal_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:59:17.531354+00:00
-- url     : https://prove2.me/theorems/9370d15f-8bec-41dc-883f-fae1512e0a6d
-- title:
--   Adelic GLn: diagonal apply
-- statement:
--   The Adelic GLn construction uses the diagonal apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L240-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L240-L242

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

theorem GroundTheory.Automorphic.AdelicGLn.diagonal_apply (γ : GL (Fin n) K) (a b : Fin n) :
    diagonal K n γ a b = algebraMap K 𝔸[K] (γ a b) := by sorry

attribute [defeq] GroundTheory.Automorphic.AdelicGLn.diagonal_apply
