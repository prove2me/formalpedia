-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_NormalRepresentationLattice_nfBasis_val
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_val
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:14.701285+00:00
-- url     : https://prove2.me/theorems/39bbe713-8568-545c-b534-fa98e96dbdef
-- title:
--   Normal Representation Lattice: nf Basis val
-- statement:
--   The Normal Representation Lattice construction uses the nf Basis val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/NormalRepresentationLattice.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/NormalRepresentationLattice.lean#L16-L21

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_val (ϖ : kˣ) (g : GL n k) (e : Fin c → ℤ) (z : n → k) : (nfBasis ϖ g e z).val =
    fromBlocks g.val (Matrix.of fun r i => if i.val = 0 then z r * (ϖ : k) ^ e i else 0) 0
      (diagonal fun i => (ϖ : k) ^ e i) := by sorry
