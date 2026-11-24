-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_eq_of_map_eval_eq_of_dense
-- name    : GlobalTheory.SimpleRoots.eq_of_map_eval_eq_of_dense
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:13:35.144712+00:00
-- url     : https://prove2.me/theorems/7be19f12-dc88-4a7b-b465-87e5737fe7a8
-- title:
--   Simple Roots: eq of map eval eq of dense
-- statement:
--   The Simple Roots construction uses the eq of map eval eq of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L105-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L105-L114

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

theorem GlobalTheory.SimpleRoots.eq_of_map_eval_eq_of_dense {a b : Polynomial (MvPolynomial (Fin d) ℂ)}
    {U : Set (Fin d → ℂ)} (hU : Dense U)
    (h : ∀ x ∈ U, a.map (MvPolynomial.eval x) = b.map (MvPolynomial.eval x)) : a = b := by sorry
