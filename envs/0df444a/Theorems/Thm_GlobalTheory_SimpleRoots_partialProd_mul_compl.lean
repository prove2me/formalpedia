-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_partialProd_mul_compl
-- name    : GlobalTheory.SimpleRoots.partialProd_mul_compl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:14.833801+00:00
-- url     : https://prove2.me/theorems/d990567a-8b2f-44b8-9829-183a0e1858e9
-- title:
--   Simple Roots: partial Prod mul compl
-- statement:
--   The Simple Roots construction uses the partial Prod mul compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L32-L41

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

theorem GlobalTheory.SimpleRoots.partialProd_mul_compl {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) :
    partialProd p u x * partialProd p uᶜ x = p.map (MvPolynomial.eval x) := by sorry
