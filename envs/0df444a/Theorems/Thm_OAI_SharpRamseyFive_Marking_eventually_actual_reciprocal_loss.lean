-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_Marking_eventually_actual_reciprocal_loss
-- name    : OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:01:59.674111+00:00
-- url     : https://prove2.me/theorems/3d12ecc8-6c33-4a86-b664-bb528d6a7afc
-- title:
--   OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss` of [lean/OAI/Combinatorics/RamseyFive/Marking/WindowSmallFailure.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/WindowSmallFailure.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.Marking`, with `open Module ProjectiveIncidence FiniteEntropy Windows`, `open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy`, `open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology`):
--
--   ```lean
--   theorem eventually_actual_reciprocal_loss {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D k J lo hi B : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (q₀ : ℕ) (K V κ : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [CharP K q₀] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ],
--       ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n H steps rem : ℕ) [Nonempty (Fin n)]
--         (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
--         (elig : κ→(Fin w×Bool)→Finset (Fin n)) (u : κ→Slots w n→ℝ)
--         (hcap : ∀a,0<μ a→ReciprocalCaps (p a) (u a) C₀)
--         (hcons : ∀a,0<μ a→∀x,0<p a x→∀i j,slotEmbedding i < slotEmbedding j→
--           Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
--         (hu : ∀a,0<μ a→∀i,lo≤u a i ∧ u a i≤hi)
--         (hlohi : lo≤hi) (hk : 0<k) (hJ : 4*Real.log (Nat.card K)≤J)
--         (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
--         (hcard : Nat.card K=q₀) (hrange : Range η σ D R) (hL : (L₀:ℝ)=L η σ D)
--         (hb0 : 0≤k+2*(D*σ^(2*beta η))+Real.log 4)
--         (hbhi : k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η))
--         (hw : w<2^H) (hH : (H:ℝ)≤σ^beta η)
--         (hmass : reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2)
--         (hsmall : 2*(D*σ^beta η+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/(D*σ^(2*beta η))+
--           2*Real.exp 1*reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2)
--         (_hε : ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*(Nat.card K:ℝ)))
--         (_hrem : 0 < rem) (_hn : n≤2*rem)
--         (_hS : ∀a,0<μ a→∀b,rem+steps≤(elig a b).card)
--         (_hbad : mean (preRoundLaw μ p elig steps) (fun z=>
--           ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
--             preRoundBad μ p elig steps J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
--               (historyCollision p u (D*σ^(2*beta η))) z j)≤B),
--         let s:=D*σ^(2*beta η)
--         let d:=D*σ^beta η
--         let ε:=σ^(-2000*beta η)/Real.exp σ
--         let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
--           (P η σ D R) (σ^(-800*beta η)) R L₀
--         let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
--           (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
--           (P η σ D R) (σ^(-800*beta η)) R L₀
--         let E:=actualWindowSet μ p u J d ε s k
--         ∃ W : ∀z,∀hE : (E z).Nonempty,
--           ReciprocalWindows (windowPosterior p z) (u z.1.1) z.2 (survivingOriginal (E z) hE) s,
--         mean (preRoundLaw μ p elig steps) (fun h=>
--           mean (allWindowExperiment f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)) (fun z=>
--             ((allWindowPositions f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)
--               σ hσ hq hd.le (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num)
--               (preRoundBad μ p elig steps J d ε (historyCollision p u s) h)
--               z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
--           5*B+(2*n:ℝ)*((hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k)+(w*(2*n):ℝ)*ρ
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.BlockHistory`, `OAI.SharpRamseyFive.FiniteEntropy.Law`, `OAI.SharpRamseyFive.FiniteEntropy.blockActive`, `OAI.SharpRamseyFive.FiniteEntropy.blockHistoryFintype`, `OAI.SharpRamseyFive.FiniteEntropy.historyUnused`, `OAI.SharpRamseyFive.FiniteEntropy.mean`, `OAI.SharpRamseyFive.FiniteEntropy.preRoundBad`, `OAI.SharpRamseyFive.FiniteEntropy.preRoundLaw`, `OAI.SharpRamseyFive.Marking.FlagPair`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident`, `OAI.SharpRamseyFive.ProjectiveIncidence.bidualPoint`, `OAI.SharpRamseyFive.ScoreGeometry.FinitePredictor` and `OAI.SharpRamseyFive.Windows.Slots` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.Marking.arlTDE`, `OAI.SharpRamseyFive.Marking.reciprocalBadMass`, `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.PivotTree.finiteBalanced`, `OAI.SharpRamseyFive.PivotTree.survivingOriginal` and `OAI.SharpRamseyFive.ProjectiveIncidence.PivotContext` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.Marking.ReciprocalCaps`, `OAI.SharpRamseyFive.Marking.ReciprocalWindows`, `OAI.SharpRamseyFive.Marking.WindowHistory`, `OAI.SharpRamseyFive.Marking.WindowLevelsData`, `OAI.SharpRamseyFive.Marking.actualWindowSet`, `OAI.SharpRamseyFive.Marking.historyCollision`, `OAI.SharpRamseyFive.Marking.windowPosterior` and `OAI.SharpRamseyFive.Windows.slotEmbedding` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.Marking.allWindowIDE`, `OAI.SharpRamseyFive.ProjectiveIncidence.OrientedPivotTreeTape`, `OAI.SharpRamseyFive.ProjectiveIncidence.VariableTreeTape`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype` and `OAI.SharpRamseyFive.ScoreGeometry.fourFinitePredictor` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.Marking.allWindowExperiment`, `OAI.SharpRamseyFive.Marking.allWindowPositions` and `OAI.SharpRamseyFive.Marking.arlIDE` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/WindowSmallFailure.lean (declaration OAI.SharpRamseyFive.Marking.eventually_actual_reciprocal_loss)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section

attribute [local irreducible] actualWindows actualWindowSet

attribute [local instance] OAI.SharpRamseyFive.Marking.arlTDE
attribute [local instance] OAI.SharpRamseyFive.Marking.arlIDE
local instance arlBDEFix (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance arlTDEFix (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
theorem eventually_actual_reciprocal_loss {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k J lo hi B : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V κ : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ],
    ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n H steps rem : ℕ) [Nonempty (Fin n)]
      (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
      (elig : κ→(Fin w×Bool)→Finset (Fin n)) (u : κ→Slots w n→ℝ)
      (hcap : ∀a,0<μ a→ReciprocalCaps (p a) (u a) C₀)
      (hcons : ∀a,0<μ a→∀x,0<p a x→∀i j,slotEmbedding i < slotEmbedding j→
        Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
      (hu : ∀a,0<μ a→∀i,lo≤u a i ∧ u a i≤hi)
      (hlohi : lo≤hi) (hk : 0<k) (hJ : 4*Real.log (Nat.card K)≤J)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
      (hcard : Nat.card K=q₀) (hrange : Range η σ D R) (hL : (L₀:ℝ)=L η σ D)
      (hb0 : 0≤k+2*(D*σ^(2*beta η))+Real.log 4)
      (hbhi : k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η))
      (hw : w<2^H) (hH : (H:ℝ)≤σ^beta η)
      (hmass : reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2)
      (hsmall : 2*(D*σ^beta η+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/(D*σ^(2*beta η))+
        2*Real.exp 1*reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2)
      (_hε : ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*(Nat.card K:ℝ)))
      (_hrem : 0 < rem) (_hn : n≤2*rem)
      (_hS : ∀a,0<μ a→∀b,rem+steps≤(elig a b).card)
      (_hbad : mean (preRoundLaw μ p elig steps) (fun z=>
        ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
          preRoundBad μ p elig steps J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
            (historyCollision p u (D*σ^(2*beta η))) z j)≤B),
      let s:=D*σ^(2*beta η)
      let d:=D*σ^beta η
      let ε:=σ^(-2000*beta η)/Real.exp σ
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let E:=actualWindowSet μ p u J d ε s k
      ∃ W : ∀z,∀hE : (E z).Nonempty,
        ReciprocalWindows (windowPosterior p z) (u z.1.1) z.2 (survivingOriginal (E z) hE) s,
      mean (preRoundLaw μ p elig steps) (fun h=>
        mean (allWindowExperiment f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)) (fun z=>
          ((allWindowPositions f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)
            σ hσ hq hd.le (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num)
            (preRoundBad μ p elig steps J d ε (historyCollision p u s) h)
            z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
        5*B+(2*n:ℝ)*((hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k)+(w*(2*n):ℝ)*ρ := by
  sorry
end

end SharpRamseyFive.Marking

end OAI
end
