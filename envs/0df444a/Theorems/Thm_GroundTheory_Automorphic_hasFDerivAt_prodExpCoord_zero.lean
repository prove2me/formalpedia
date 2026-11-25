-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFDerivAt_prodExpCoord_zero
-- name    : GroundTheory.Automorphic.hasFDerivAt_prodExpCoord_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:44.442832+00:00
-- url     : https://prove2.me/theorems/b1444b27-f2cf-4bdc-92e1-b63ef511cac9
-- title:
--   Automorphic: has FDeriv At prod Exp Coord zero
-- statement:
--   The Automorphic construction uses the has FDeriv At prod Exp Coord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L121-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L121-L134

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

theorem GroundTheory.Automorphic.hasFDerivAt_prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    HasFDerivAt (prodExpCoord b)
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
        (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) 0 := by sorry
