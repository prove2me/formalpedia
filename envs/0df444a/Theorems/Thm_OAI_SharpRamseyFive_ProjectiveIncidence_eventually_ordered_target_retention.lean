-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_eventually_ordered_target_retention
-- name    : OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:03:04.200179+00:00
-- url     : https://prove2.me/theorems/85582bcd-d5f3-4f9e-b557-eb91e02b3af8
-- title:
--   OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention` of [lean/OAI/Combinatorics/RamseyFive/Geometry/OrderedTargetRetention.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/OrderedTargetRetention.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ProjectiveIncidence`, with `open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy`, `open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology`):
--
--   ```lean
--   theorem eventually_ordered_target_retention {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0 ≤ Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [CharP K q₀] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [Fintype (ℙ K (Dual K (Dual K V)))],
--       ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
--         (A B : I → Type) [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
--         (μ : ∀ i,Law (A i)) (ν : ∀ i,Law (B i))
--         (X : ∀ i,A i → Finset (ℙ K V)) (Y : ∀ i,B i → Finset (ℙ K (Dual K V)))
--         (hX : ∀ i a,(X i a).Nonempty) (hY : ∀ i b,(Y i b).Nonempty)
--         (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
--         (F ε : ℝ) (hF : 0 ≤ F) (hε : 0 ≤ ε)
--         (hμ : ∀ i a,(∑ s,μ i s*uniformWeight (X i s) a) ≤ F*p i a)
--         (hν : ∀ i b,(∑ t,ν i t*uniformWeight (Y i t) b) ≤ F*q i b)
--         (hsparse : ∀ i j,i ≤ j → relationMass Incident (p i) (q j) ≤ ε)
--         (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
--         Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
--         0 ≤ b → b ≤ Cb*D*σ^(6*beta η) →
--         (∀ i a d,(Nat.card K:ℝ)^5*Real.exp (-b) ≤ ((X i a).card:ℝ)*(Y i d).card) →
--         let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
--           (P η σ D R) (σ^(-800*beta η)) R L₀
--         let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
--           (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
--           (P η σ D R) (σ^(-800*beta η)) R L₀
--         ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree),
--         ∀ (Ω : Type) [Fintype Ω] (γ : Law Ω) (a : Ω → ℙ K V) (b₀ : Ω → ℙ K (Dual K V))
--           (goodA : ℙ K V → Prop) (goodB : ℙ K (Dual K V) → Prop) (ε₀ : ℝ),0 ≤ ε₀ →
--           (∀ i,label tree j ≤ i → relationMass Incident (fun x=>if goodA x then map γ a x else 0) (q i) ≤ ε₀) →
--           (∀ i,i ≤ label tree j → relationMass Incident (p i) (fun y=>if goodB y then map γ b₀ y else 0) ≤ ε₀) →
--         orientedTargetFailure f r σ hσ hq hd.le μ ν X Y hX hY γ a b₀
--           (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree j ≤
--         eventMass γ (Finset.univ.filter fun x=>¬goodA (a x))+
--         eventMass γ (Finset.univ.filter fun x=>¬goodB (b₀ x))+
--         tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2*ε+
--           ((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2*ε+5*Real.exp (-(Nat.card K:ℝ)))+
--         (20*tree.height+2)*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F*ε₀
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.Law`, `OAI.SharpRamseyFive.FiniteEntropy.eventMass`, `OAI.SharpRamseyFive.FiniteEntropy.map`, `OAI.SharpRamseyFive.FiniteEntropy.relationMass`, `OAI.SharpRamseyFive.FiniteEntropy.uniformWeight`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident`, `OAI.SharpRamseyFive.ProjectiveIncidence.bidualPoint` and `OAI.SharpRamseyFive.ScoreGeometry.FinitePredictor` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.ProjectiveIncidence.PivotContext`, `OAI.SharpRamseyFive.ProjectiveIncidence.orderedTargetPropDecidable`, `OAI.SharpRamseyFive.TreeCodec.Address`, `OAI.SharpRamseyFive.TreeCodec.Ordered` and `OAI.SharpRamseyFive.TreeCodec.label` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ScoreGeometry.fourFinitePredictor` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.orientedTargetFailure` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.Marking.eventually_window_failure_small` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/OrderedTargetRetention.lean (declaration OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section

local instance (priority := high) orderedTargetPropDecidable_rda1347_1 (P : Prop) : Decidable P := Classical.propDecidable P
variable {K V I Ω : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Fintype I] [DecidableEq I] [Fintype Ω]
  {A B : I → Type} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]

theorem eventually_ordered_target_retention {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
      (A B : I → Type) [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
      (μ : ∀ i,Law (A i)) (ν : ∀ i,Law (B i))
      (X : ∀ i,A i → Finset (ℙ K V)) (Y : ∀ i,B i → Finset (ℙ K (Dual K V)))
      (hX : ∀ i a,(X i a).Nonempty) (hY : ∀ i b,(Y i b).Nonempty)
      (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
      (F ε : ℝ) (hF : 0 ≤ F) (hε : 0 ≤ ε)
      (hμ : ∀ i a,(∑ s,μ i s*uniformWeight (X i s) a) ≤ F*p i a)
      (hν : ∀ i b,(∑ t,ν i t*uniformWeight (Y i t) b) ≤ F*q i b)
      (hsparse : ∀ i j,i ≤ j → relationMass Incident (p i) (q j) ≤ ε)
      (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
      0 ≤ b → b ≤ Cb*D*σ^(6*beta η) →
      (∀ i a d,(Nat.card K:ℝ)^5*Real.exp (-b) ≤ ((X i a).card:ℝ)*(Y i d).card) →
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree),
      ∀ (Ω : Type) [Fintype Ω] (γ : Law Ω) (a : Ω → ℙ K V) (b₀ : Ω → ℙ K (Dual K V))
        (goodA : ℙ K V → Prop) (goodB : ℙ K (Dual K V) → Prop) (ε₀ : ℝ),0 ≤ ε₀ →
        (∀ i,label tree j ≤ i → relationMass Incident (fun x=>if goodA x then map γ a x else 0) (q i) ≤ ε₀) →
        (∀ i,i ≤ label tree j → relationMass Incident (p i) (fun y=>if goodB y then map γ b₀ y else 0) ≤ ε₀) →
      orientedTargetFailure f r σ hσ hq hd.le μ ν X Y hX hY γ a b₀
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree j ≤
      eventMass γ (Finset.univ.filter fun x=>¬goodA (a x))+
      eventMass γ (Finset.univ.filter fun x=>¬goodB (b₀ x))+
      tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2*ε+
        ((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2*ε+5*Real.exp (-(Nat.card K:ℝ)))+
      (20*tree.height+2)*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F*ε₀ := by
  sorry
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end
