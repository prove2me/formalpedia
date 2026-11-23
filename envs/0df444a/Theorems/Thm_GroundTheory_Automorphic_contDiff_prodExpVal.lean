-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_contDiff_prodExpVal
-- name    : GroundTheory.Automorphic.contDiff_prodExpVal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:35.4153+00:00
-- url     : https://prove2.me/theorems/27cdf73b-d055-4253-86a2-e6fe87835b3e
-- title:
--   Automorphic: cont Diff prod Exp Val
-- statement:
--   The Automorphic construction uses the cont Diff prod Exp Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L26-L36

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

theorem GroundTheory.Automorphic.contDiff_prodExpVal {d : ℕ} (X : Fin d → 𝔸) : ContDiff ℝ ∞ (prodExpVal X) := by sorry
