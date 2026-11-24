-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_exists_norm_coeff_partialProd_le
-- name    : GlobalTheory.SimpleRoots.exists_norm_coeff_partialProd_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:13:13.992011+00:00
-- url     : https://prove2.me/theorems/a39a14e1-67f9-4229-ab61-4bd96ef24b6d
-- title:
--   Simple Roots: exists norm coeff partial Prod le
-- statement:
--   The Simple Roots construction uses the exists norm coeff partial Prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L43-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L43-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SimpleRoots
open Polynomial
variable {d : ℕ}

theorem GlobalTheory.SimpleRoots.exists_norm_coeff_partialProd_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) :
    ∃ (C : ℝ) (m : ℕ), ∀ k x, ‖(partialProd p u x).coeff k‖ ≤ C * (1 + ‖x‖) ^ m := by sorry
