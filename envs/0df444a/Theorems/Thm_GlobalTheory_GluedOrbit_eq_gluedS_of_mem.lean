-- Prove2me | Theorems.Thm_GlobalTheory_GluedOrbit_eq_gluedS_of_mem
-- name    : GlobalTheory.GluedOrbit.eq_gluedS_of_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:19.873992+00:00
-- url     : https://prove2.me/theorems/77ff6ee0-a39d-4f15-b9d5-36a13e94e58a
-- title:
--   Glued Orbit: eq glued S of mem
-- statement:
--   The Glued Orbit construction uses the eq glued S of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmulGluedLatticeFirstPositionCases.lean#L16-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmulGluedLatticeFirstPositionCases.lean#L16-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCases
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
noncomputable section
open GlobalTheory GlobalTheory.GluedOrbit
open GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration (interX)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}

theorem GlobalTheory.GluedOrbit.eq_gluedS_of_mem (q : Unif k) {M : Submodule 𝒪[k] (n ⊕ Fin 1 → k)}
    (hq : ∀ x ∈ M, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) {m : n ⊕ Fin 1 → k} (hm : m ∈ M)
    (hm1 : m (Sum.inr 0) = q.inv) : M = gluedS q 1 (interX M) (m ∘ Sum.inl) := by sorry
