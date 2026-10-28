-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_Marking_eventually_window_failure_small
-- name    : OAI.SharpRamseyFive.Marking.eventually_window_failure_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:01:20.782821+00:00
-- url     : https://prove2.me/theorems/713c98d4-60bd-45a3-9a9c-6d3a7862d774
-- title:
--   OAI.SharpRamseyFive.Marking.eventually_window_failure_small: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.Marking.eventually_window_failure_small` of [lean/OAI/Combinatorics/RamseyFive/Marking/WindowSmallFailure.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/WindowSmallFailure.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.Marking`, with `open Module FiniteEntropy ProjectiveIncidence Windows`, `open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy`, `open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology`):
--
--   ```lean
--   theorem eventually_window_failure_small {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D k J : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [CharP K q₀] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [Fintype (ℙ K (Dual K (Dual K V)))],
--       ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n H : ℕ) [Nonempty (Fin n)]
--         (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ)
--         (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
--         (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) (D*σ^(2*beta η)))
--         (hcons : ∀x,0<p x→∀i j,slotEmbedding i < slotEmbedding j→
--           Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
--         (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
--         (hA : ∀i,((support (first (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u i))
--         (hB : ∀i,((support (second (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (u i))
--         (_hflag : ∀i,((support (map p (fun x=>x i))).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
--         (_hJ : 4*Real.log (Nat.card K)≤J)
--         (_hgood : ∀v∈E,indexBad J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) p
--           (orderedCollision p (slotEquiv w n) u (D*σ^(2*beta η))) sel (earlySlot sel v)=0)
--         (_hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
--         (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
--         Nat.card K=q₀→Range η σ D R→(L₀:ℝ)=L η σ D→
--         0≤k+2*(D*σ^(2*beta η))+Real.log 4→
--         k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η)→
--         w<2^H→(H:ℝ)≤σ^beta η→
--         let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
--           (P η σ D R) (σ^(-800*beta η)) R L₀
--         let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
--           (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
--           (P η σ D R) (σ^(-800*beta η)) R L₀
--         ∀ (v : Fin w) (_hv : v∈E) (t : Fin (2*n)),
--         indexBad J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) p
--           (orderedCollision p (slotEquiv w n) u (D*σ^(2*beta η))) sel (middleSlot v t)=0→
--         allWindowFailure f r p u sel E W σ hσ hq hd.le
--           (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) v t≤ρ
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.Law`, `OAI.SharpRamseyFive.FiniteEntropy.first`, `OAI.SharpRamseyFive.FiniteEntropy.indexBad`, `OAI.SharpRamseyFive.FiniteEntropy.map`, `OAI.SharpRamseyFive.FiniteEntropy.second`, `OAI.SharpRamseyFive.FiniteEntropy.support`, `OAI.SharpRamseyFive.Marking.FlagPair`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident`, `OAI.SharpRamseyFive.ProjectiveIncidence.bidualPoint`, `OAI.SharpRamseyFive.ScoreGeometry.FinitePredictor` and `OAI.SharpRamseyFive.Windows.Slots` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.PivotTree.survivingOriginal` and `OAI.SharpRamseyFive.ProjectiveIncidence.PivotContext` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.Marking.ReciprocalWindows`, `OAI.SharpRamseyFive.Marking.orderedCollision`, `OAI.SharpRamseyFive.Windows.earlySlot`, `OAI.SharpRamseyFive.Windows.lateSlot`, `OAI.SharpRamseyFive.Windows.slotEmbedding` and `OAI.SharpRamseyFive.Windows.slotEquiv` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ScoreGeometry.fourFinitePredictor` and `OAI.SharpRamseyFive.Windows.middleSlot` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.Marking.allWindowFailure` and `OAI.SharpRamseyFive.Marking.smallFailureIDE` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/WindowSmallFailure.lean (declaration OAI.SharpRamseyFive.Marking.eventually_window_failure_small)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module FiniteEntropy ProjectiveIncidence Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section

attribute [local instance] OAI.SharpRamseyFive.Marking.smallFailureIDE
theorem eventually_window_failure_small {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k J : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n H : ℕ) [Nonempty (Fin n)]
      (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ)
      (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
      (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) (D*σ^(2*beta η)))
      (hcons : ∀x,0<p x→∀i j,slotEmbedding i < slotEmbedding j→
        Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
      (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
      (hA : ∀i,((support (first (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u i))
      (hB : ∀i,((support (second (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (u i))
      (_hflag : ∀i,((support (map p (fun x=>x i))).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
      (_hJ : 4*Real.log (Nat.card K)≤J)
      (_hgood : ∀v∈E,indexBad J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) p
        (orderedCollision p (slotEquiv w n) u (D*σ^(2*beta η))) sel (earlySlot sel v)=0)
      (_hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀→Range η σ D R→(L₀:ℝ)=L η σ D→
      0≤k+2*(D*σ^(2*beta η))+Real.log 4→
      k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η)→
      w<2^H→(H:ℝ)≤σ^beta η→
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (v : Fin w) (_hv : v∈E) (t : Fin (2*n)),
      indexBad J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) p
        (orderedCollision p (slotEquiv w n) u (D*σ^(2*beta η))) sel (middleSlot v t)=0→
      allWindowFailure f r p u sel E W σ hσ hq hd.le
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) v t≤ρ := by
  sorry
end
end

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology

end SharpRamseyFive.Marking

end OAI
end
