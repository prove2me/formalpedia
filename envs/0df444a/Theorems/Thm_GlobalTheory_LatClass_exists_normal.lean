-- Prove2me | Theorems.Thm_GlobalTheory_LatClass_exists_normal
-- name    : GlobalTheory.LatClass.exists_normal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:42.503432+00:00
-- url     : https://prove2.me/theorems/49f42ae8-4723-5e25-826a-91c548fab51a
-- title:
--   Lat Class: exists normal
-- statement:
--   The Lat Class construction uses the exists normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeClasses.lean#L46-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LatticeClasses.lean#L46-L66

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
include hϖ hψ hb hs hp hJ

theorem GlobalTheory.LatClass.exists_normal {A : RepFam k s X} (hA : T.IsRepSystem A ψ ν) (j : ℕ) :
    ∀ c h, ∀ g ∈ A j c h, ∃ r ∈ R k (X j) (c + 1) 1, IsNormalRep T ϖ j c h (r * g) := by sorry
