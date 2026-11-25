-- Prove2me | Theorems.Thm_GlobalTheory_Mass_LatticeGens_card_map_mkQ
-- name    : GlobalTheory.Mass.LatticeGens.card_map_mkQ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:59:40.932878+00:00
-- url     : https://prove2.me/theorems/426ad42c-a040-56ab-ba8b-5f4c59a714b7
-- title:
--   Lattice Gens: card map mk Q
-- statement:
--   The Lattice Gens construction uses the card map mk Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeQuotientGensAndIntermediateCount.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeQuotientGensAndIntermediateCount.lean#L86-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LatticeGens
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem GlobalTheory.Mass.LatticeGens.card_map_mkQ (A B : Submodule R V) : Nat.card (B.map A.mkQ) = idxN B A := by sorry
