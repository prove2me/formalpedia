-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_eventually_ordered_tree_missing
-- name    : OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:04:55.269067+00:00
-- url     : https://prove2.me/theorems/8f43f25b-1430-43f0-9319-b95e968c7d59
-- title:
--   OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing` of [lean/OAI/Combinatorics/RamseyFive/Entropy/OrderedRetention.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/OrderedRetention.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ProjectiveIncidence`, with `open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy`, `open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology`):
--
--   ```lean
--   theorem eventually_ordered_tree_missing {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0 ≤ Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [CharP K q₀] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [Fintype (ℙ K (Dual K (Dual K V)))],
--       ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
--         (A B : I  →  Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
--         (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
--         (X : ∀ i, A i  →  Finset (ℙ K V)) (Y : ∀ i, B i  →  Finset (ℙ K (Dual K V)))
--         (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
--         (p : I  →  Law (ℙ K V)) (q : I  →  Law (ℙ K (Dual K V)))
--         (F ε : ℝ) (hF : 0 ≤ F) (hε : 0 ≤ ε)
--         (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a)  ≤  F*p i a)
--         (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b)  ≤  F*q i b)
--         (hsparse : ∀ i j,i ≤ j → relationMass Incident (p i) (q j) ≤ ε)
--         (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
--         Nat.card K=q₀  →  Range η σ D R  →  (L₀:ℝ)=L η σ D  →
--         0 ≤ b  →  b ≤ Cb*D*σ^(6*beta η)  →
--         (∀ i a d, (Nat.card K:ℝ)^5*Real.exp (-b) ≤ ((X i a).card:ℝ)*(Y i d).card)  →
--         let f := fun C : PivotContext K V =>
--           fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
--         let r := fun C : PivotContext K V =>
--           fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
--             (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
--         ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree),
--       (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
--         (Finset.univ.filter (fun ω =>
--           orientedPivotSuccessAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
--             (fun i => hX i _) (fun i => hY i _) (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω (Finset.univ,Finset.univ) j = none)))  ≤
--         tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2*ε+
--           ((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2*ε+5*Real.exp (-(Nat.card K:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.Law`, `OAI.SharpRamseyFive.FiniteEntropy.eventMass`, `OAI.SharpRamseyFive.FiniteEntropy.originalLevelLaw`, `OAI.SharpRamseyFive.FiniteEntropy.relationMass`, `OAI.SharpRamseyFive.FiniteEntropy.uniformWeight`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident`, `OAI.SharpRamseyFive.ProjectiveIncidence.bidualPoint` and `OAI.SharpRamseyFive.ScoreGeometry.FinitePredictor` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.ProjectiveIncidence.PivotContext`, `OAI.SharpRamseyFive.ProjectiveIncidence.orderedRetentionPropDecidable`, `OAI.SharpRamseyFive.TreeCodec.Address` and `OAI.SharpRamseyFive.TreeCodec.Ordered` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.OrientedPivotTreeTape`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeLaw`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype` and `OAI.SharpRamseyFive.ScoreGeometry.fourFinitePredictor` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotSuccessAt` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/OrderedRetention.lean (declaration OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing)

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

local instance (priority := high) orderedRetentionPropDecidable_r36345b_1 (P : Prop) : Decidable P := Classical.propDecidable P
theorem eventually_ordered_tree_missing {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
      (A B : I  →  Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
      (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
      (X : ∀ i, A i  →  Finset (ℙ K V)) (Y : ∀ i, B i  →  Finset (ℙ K (Dual K V)))
      (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
      (p : I  →  Law (ℙ K V)) (q : I  →  Law (ℙ K (Dual K V)))
      (F ε : ℝ) (hF : 0 ≤ F) (hε : 0 ≤ ε)
      (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a)  ≤  F*p i a)
      (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b)  ≤  F*q i b)
      (hsparse : ∀ i j,i ≤ j → relationMass Incident (p i) (q j) ≤ ε)
      (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀  →  Range η σ D R  →  (L₀:ℝ)=L η σ D  →
      0 ≤ b  →  b ≤ Cb*D*σ^(6*beta η)  →
      (∀ i a d, (Nat.card K:ℝ)^5*Real.exp (-b) ≤ ((X i a).card:ℝ)*(Y i d).card)  →
      let f := fun C : PivotContext K V =>
        fourFinitePredictor hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V =>
        fourFinitePredictor (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2
          (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree),
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω =>
        orientedPivotSuccessAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree ω (Finset.univ,Finset.univ) j = none)))  ≤
      tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*F^2*ε+
        ((Nat.card K:ℝ)/(σ^(-1000*beta η)))*F^2*ε+5*Real.exp (-(Nat.card K:ℝ))) := by
  sorry
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end
