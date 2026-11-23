-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isOpen_prodExpCoord_domain
-- name    : GroundTheory.Automorphic.isOpen_prodExpCoord_domain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:39.014232+00:00
-- url     : https://prove2.me/theorems/9da360fa-cce5-4ef8-a605-a027f0712669
-- title:
--   Automorphic: is Open prod Exp Coord domain
-- statement:
--   The Automorphic construction uses the is Open prod Exp Coord domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L117-L119

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}

theorem GroundTheory.Automorphic.isOpen_prodExpCoord_domain {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    IsOpen {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} := by sorry
