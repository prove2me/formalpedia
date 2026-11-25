-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_om_per
-- name    : GlobalTheory.LatClass.om_per
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:49:29.982751+00:00
-- url     : https://prove2.me/theorems/cfbf1f4b-0447-43df-85ff-5dc1b1ddf4cb
-- title:
--   Lat Class: om per
-- statement:
--   The Lat Class construction uses the om per property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L195-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZpowMulMemPow.lean#L195-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.LatClass.om_per (hϖ : valuation k (ϖ : k) = uniformizer k) {μ : kˣ →* ℂˣ} {Φ : Matrix Y Y' k → ℂ}
    (hp : ∀ x y, MaxM y → Φ (x + y) = Φ x) (g : GL Y' k) (h : GL Y k)
    (x y : Matrix Y Y' k) (hy : MapsLat y (latOf g) (latOf h)) :
    om μ g h Φ (x + (ϖ : k) • y) = om μ g h Φ x := by sorry
