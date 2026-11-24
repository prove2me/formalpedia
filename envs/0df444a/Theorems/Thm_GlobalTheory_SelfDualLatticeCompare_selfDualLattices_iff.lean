-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_selfDualLattices_iff
-- name    : GlobalTheory.SelfDualLatticeCompare.selfDualLattices_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:01.998807+00:00
-- url     : https://prove2.me/theorems/1fc4c0ad-9bac-407c-b3e3-1bd06d904622
-- title:
--   Self Dual Lattice Compare: self Dual Lattices iff
-- statement:
--   The Self Dual Lattice Compare construction uses the self Dual Lattices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L194-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L194-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.SelfDualLatticeCompare

theorem GlobalTheory.SelfDualLatticeCompare.selfDualLattices_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.SelfDualLattices ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas := by sorry
