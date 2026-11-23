-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_card_roots_map
-- name    : GlobalTheory.SimpleRoots.card_roots_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:50.422815+00:00
-- url     : https://prove2.me/theorems/d79be3f0-7ec3-4de2-b75b-a4bd936a0f45
-- title:
--   Simple Roots: card roots map
-- statement:
--   The Simple Roots construction uses the card roots map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L21-L23

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

theorem GlobalTheory.SimpleRoots.card_roots_map {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) (x : Fin d → ℂ) :
    (p.map (MvPolynomial.eval x)).roots.card = p.natDegree := by sorry
