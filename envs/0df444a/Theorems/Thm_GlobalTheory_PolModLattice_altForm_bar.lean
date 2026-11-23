-- Prove2me | Theorems.Thm_GlobalTheory_PolModLattice_altForm_bar
-- name    : GlobalTheory.PolModLattice.altForm_bar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:10:52.723806+00:00
-- url     : https://prove2.me/theorems/25d68813-2039-4d5a-bd53-53519efa7828
-- title:
--   Pol Mod Lattice: alt Form bar
-- statement:
--   The Pol Mod Lattice construction uses the alt Form bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDual.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDual.lean#L46-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.PolModLattice.altForm_bar (x y : E) : bar (altForm x y) = - altForm x y := by sorry
