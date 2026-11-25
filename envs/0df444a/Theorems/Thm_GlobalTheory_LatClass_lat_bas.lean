-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_lat_bas
-- name    : GlobalTheory.LatClass.lat_bas
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:03.845836+00:00
-- url     : https://prove2.me/theorems/45d358be-6221-4650-8722-f34e5643e9ac
-- title:
--   Lat Class: lat bas
-- statement:
--   The Lat Class construction uses the lat bas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeClasses.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeClasses.lean#L33-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsValuationEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MulMemOfHatCosetIndNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatNeZeroOfMemR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeClasses
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
  {T : Chain k s X Z} {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
  (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
  (hb : ∀ j c h, latOf (T.bas j c h) = latOf 1)
  (hs : ∀ j c h x, T.Phi j c h x ≠ 0 → IntM x)
  (hp : ∀ j c h x y, MaxM y → T.Phi j c h (x + y) = T.Phi j c h x)
  (hJ : ∀ j c h, (T.lev j c h).J ≤ KO k (X j ⊕ Fin c))
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
include hb

theorem GlobalTheory.LatClass.lat_bas {j c h} (g : GL (X j ⊕ Fin c) k) : latOf (g * T.bas j c h) = latOf g := by sorry
