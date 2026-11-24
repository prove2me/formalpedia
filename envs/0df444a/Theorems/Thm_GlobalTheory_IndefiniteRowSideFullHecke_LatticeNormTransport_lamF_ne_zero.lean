-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LatticeNormTransport_lamF_ne_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:09.990846+00:00
-- url     : https://prove2.me/theorems/ad786a71-1cac-4881-acf5-8fff4908fa27
-- title:
--   Lattice Norm Transport: lam F ne zero
-- statement:
--   The Lattice Norm Transport construction uses the lam F ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/LatticeNormTransport.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/LatticeNormTransport.lean#L107-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport

theorem GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero {E : Type} [Field E] [NumberField E] (s : ℕ) (χ : HChar E) (y : (Af E)ˣ) : lamF s χ y ≠ 0 := by sorry
