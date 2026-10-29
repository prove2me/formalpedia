-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ObservableTrajectory_omission_chain_dual
-- name    : OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T02:58:38.321991+00:00
-- url     : https://prove2.me/theorems/bac372a4-52d3-4938-a7ae-b56ef2f74b48
-- title:
--   OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual` of [lean/OAI/Combinatorics/ContingencyTables/Transport/ObservableTrajectory.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Transport/ObservableTrajectory.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ObservableTrajectory`, with `open scoped BigOperators Classical`, `open CommonBasesFPRAS BinaryContraction DegreeCompletion ObservableBounds ComplementChain`):
--
--   ```lean
--   theorem omission_chain_dual (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
--       (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
--       (f G : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r)
--       (hf : DegreePositive f gs.length) (hsig : OmissionProperty f gs.length)
--       (q : ℝ) (hq : 1 ≤ q) (hG : ClassObservable gs G)
--       (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
--       (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r)
--       (H : ChainIndex gs → ℝ) :
--       let C := metropolisChain gs hgs hne hcover w (completeDegree f gs.length) hw
--         (completeDegree_positive f gs.length hf)
--       let g := fun S : ChainIndex gs => G S.val-chainMean gs w f G
--       (C.inner g H)^2 ≤ observableConstant gs.length q*C.inner g g*C.energy H
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.ChainIndex`, `OAI.CommonBasesFPRAS.ChainState`, `OAI.CommonBasesFPRAS.ClassObservable`, `OAI.CommonBasesFPRAS.FiniteChain`, `OAI.CommonBasesFPRAS.SlotsFresh`, `OAI.CommonBasesFPRAS.chainMean`, `OAI.CommonBasesFPRAS.metropolisChain`, `OAI.CommonBasesFPRAS.pairSupport`, `OAI.CommonBasesFPRAS.slotDefect`, `OAI.CommonBasesFPRAS.slotTotal`, `OAI.CommonBasesFPRAS.FiniteChain.energy` and `OAI.CommonBasesFPRAS.FiniteChain.inner` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.BinaryContraction.DegreePositive` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.DegreeCompletion.completeDegree` and `OAI.ContingencyTables.ObservableBounds.observableConstant` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.BinaryContraction.OmissionProperty` (definitions bundle `OAIQ089A003` of this split); `OAI.ContingencyTables.DegreeCompletion.completeDegree_positive` (definitions bundle `OAIQ089A004` of this split).
--
--   **Used by.** The proof of `OAI.ContingencyTables.RootedObservationStart.observed_failure_near` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Transport/ObservableTrajectory.lean (declaration OAI.ContingencyTables.ObservableTrajectory.omission_chain_dual)

import Mathlib
import Definitions.Def_OAIQ089A003
import Definitions.Def_OAIQ089A004

section

attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.ObservableTrajectory

open scoped BigOperators Classical
open CommonBasesFPRAS BinaryContraction DegreeCompletion ObservableBounds ComplementChain

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

theorem omission_chain_dual (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f G : Set Γ → ℝ) (hw : ∀ p r, 0 < w p r)
    (hf : DegreePositive f gs.length) (hsig : OmissionProperty f gs.length)
    (q : ℝ) (hq : 1 ≤ q) (hG : ClassObservable gs G)
    (hlower : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r)
    (hupper : ∀ p ∈ gs, ∀ r ∈ gs, p ≠ r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r)
    (H : ChainIndex gs → ℝ) :
    let C := metropolisChain gs hgs hne hcover w (completeDegree f gs.length) hw
      (completeDegree_positive f gs.length hf)
    let g := fun S : ChainIndex gs => G S.val-chainMean gs w f G
    (C.inner g H)^2 ≤ observableConstant gs.length q*C.inner g g*C.energy H := by
  sorry

end ContingencyTables.ObservableTrajectory

end OAI
end
