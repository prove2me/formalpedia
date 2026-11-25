-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_NormalRepresentationLattice_nfBasis_one
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:20.214313+00:00
-- url     : https://prove2.me/theorems/b7db9648-bf15-565d-9fa4-8b54305cef5e
-- title:
--   Normal Representation Lattice: nf Basis one
-- statement:
--   The Normal Representation Lattice construction uses the nf Basis one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/NormalRepresentationLattice.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/NormalRepresentationLattice.lean#L23-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_one (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : nfBasis ϖ 1 e z = normalBasis ϖ e z := by sorry
