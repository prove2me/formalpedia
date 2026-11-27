-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_finite_hasBasis_nhds_one
-- name    : GroundTheory.Automorphic.AdelicGLn.finite_hasBasis_nhds_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:06.178532+00:00
-- url     : https://prove2.me/theorems/b0678152-837f-4ff9-805d-f5a0d75ba98b
-- title:
--   Adelic GLn: finite has Basis nhds one
-- statement:
--   The Adelic GLn construction uses the finite has Basis nhds one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L230-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean#L230-L234

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

theorem GroundTheory.Automorphic.AdelicGLn.finite_hasBasis_nhds_one :
    (𝓝 (1 : FiniteAdelicGL K n)).HasBasis
      (fun H : OpenSubgroup (FiniteAdelicGL K n) => IsCompact (H : Set (FiniteAdelicGL K n)))
      fun H => (H : Set (FiniteAdelicGL K n)) := by sorry
