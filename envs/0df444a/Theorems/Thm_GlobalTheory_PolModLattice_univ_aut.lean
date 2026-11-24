-- Prove2me | Theorems.Thm_GlobalTheory_PolModLattice_univ_aut
-- name    : GlobalTheory.PolModLattice.univ_aut
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:50:22.708184+00:00
-- url     : https://prove2.me/theorems/23c54311-2291-4261-833b-d99da15e3376
-- title:
--   Pol Mod Lattice: univ aut
-- statement:
--   The Pol Mod Lattice construction uses the univ aut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDual.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDual.lean#L50-L58

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
open Classical

theorem GlobalTheory.PolModLattice.univ_aut : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) = {1, IsCMField.complexConj E} := by sorry
