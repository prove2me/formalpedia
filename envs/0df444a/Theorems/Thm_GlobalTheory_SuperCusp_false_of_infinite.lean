-- Prove2me | Theorems.Thm_GlobalTheory_SuperCusp_false_of_infinite
-- name    : GlobalTheory.SuperCusp.false_of_infinite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:15.438066+00:00
-- url     : https://prove2.me/theorems/0a773dfe-778c-47c2-bb6b-2dc92bc080a1
-- title:
--   Super Cusp: false of infinite
-- statement:
--   The Super Cusp construction uses the false of infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L122-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L122-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp

theorem GlobalTheory.SuperCusp.false_of_infinite {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ⊕ b ≃ n) (i : a) (j : b) {z : kˣ} (hz : valuation k (z : k) < 1)
    {C : Set (GL n k)} (hC : IsCompact C) {S : Set ℕ} (hS : S.Infinite)
    (h : ∀ r ∈ S, ∃ ζ ∈ Subgroup.center (GL n k), ∃ c ∈ C,
      emb₂ k e (GeneralLinearGroup.scalar a z, 1) ^ r = ζ * c) : False := by sorry
