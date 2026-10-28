-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_protocol
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:56:59.742989+00:00
-- url     : https://prove2.me/theorems/a5119b35-1c65-4df6-95fb-d33f1cdaaa31
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol` of [lean/OAI/Combinatorics/RamseyFive/Geometry/DimensionFourHighProtocol.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/DimensionFourHighProtocol.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial`, `open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory`, `open Filter ParameterHierarchy TrainingCells MeasurePublicTable Metadata FiniteEntropy`, `open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology`):
--
--   ```lean
--   theorem eventually_four_high_protocol {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
--         [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
--         [∀x : ℙ K (I→K),Fintype (RadialLine x)],
--       ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
--         (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K (I→K))
--         (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
--         Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
--         Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
--         0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
--         (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
--         (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
--         (X.card:ℝ)=Real.exp (2*σ+g) →
--         100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) → P η σ D R/10000<g →
--         (∀j∈F,finrank K (Flat j)=3) →
--         (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
--         (∀j∈H,finrank K (Hyper j)=4) →
--         (∀V : Submodule K (I→K),finrank K V=4 → ∃j∈H,Hyper j=V) →
--       let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
--         ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
--       let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
--         ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
--       let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
--       let ht : 0<t := by positivity
--       let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
--       let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
--       let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
--       let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
--       let _hyperQueries := queryPart H hH (fun j=>flatPoints (Hyper j)) X h
--       let _flatQueries := queryPart F hF (fun j=>flatPoints (Flat j)) XH p
--       (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) →
--       let N := scoreCutoff S U (P η σ D R) τ
--       Real.log (Nat.card (TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))))≤q ∧
--       Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
--       Real.log (Fintype.card (ℙ K (I→K))+1:ℝ)+
--         Real.log (Fintype.card (ScoredPayload U S.card σ (P η σ D R) τ):ℝ)≤
--           100*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+P η σ D R) ∧
--       ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
--       let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
--       let p₀ := finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
--         (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/40) 10 R L₀ c t).map
--           (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t))
--       p₀ none≤Real.exp (-(Nat.card K:ℝ)) ∧
--       (∀W,0<p₀ (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
--         (9/40:ℝ)*X.card≤(W∩X).card)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.Law`, `OAI.SharpRamseyFive.FiniteEntropy.finiteImageLaw` and `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.GreedyTraining.clippedPart`, `OAI.SharpRamseyFive.GreedyTraining.peelLength`, `OAI.SharpRamseyFive.GreedyTraining.peelSet`, `OAI.SharpRamseyFive.GreedyTraining.queryPart`, `OAI.SharpRamseyFive.Metadata.TrainingCode`, `OAI.SharpRamseyFive.Metadata.instFintypeTrainingCode`, `OAI.SharpRamseyFive.Metadata.listCap`, `OAI.SharpRamseyFive.Metadata.productCap`, `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta`, `OAI.SharpRamseyFive.ProjectiveTraining.flatPoints`, `OAI.SharpRamseyFive.ScoreGeometry.BaseTape`, `OAI.SharpRamseyFive.ScoreGeometry.ScoredMessage`, `OAI.SharpRamseyFive.ScoreGeometry.ScoredPayload`, `OAI.SharpRamseyFive.ScoreGeometry.scoreCutoff`, `OAI.SharpRamseyFive.ScoreGeometry.scoreSearchCost` and `OAI.SharpRamseyFive.ScoreGeometry.sizeScoreCutoff` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.incidences` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ScoreGeometry.baseTapeMeasure`, `OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureBaseTapeBaseTapeMeasure`, `OAI.SharpRamseyFive.ScoreGeometry.scoredEncoded` and `OAI.SharpRamseyFive.ScoreGeometry.scoredMessageDecoded` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_finite_predictor` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/DimensionFourHighProtocol.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol)

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy TrainingCells MeasurePublicTable Metadata FiniteEntropy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_high_protocol {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (2*σ+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) → P η σ D R/10000<g →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (∀j∈H,finrank K (Hyper j)=4) →
      (∀V : Submodule K (I→K),finrank K V=4 → ∃j∈H,Hyper j=V) →
    let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
    let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
    let _hyperQueries := queryPart H hH (fun j=>flatPoints (Hyper j)) X h
    let _flatQueries := queryPart F hF (fun j=>flatPoints (Flat j)) XH p
    (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log (Nat.card (TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))))≤q ∧
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    Real.log (Fintype.card (ℙ K (I→K))+1:ℝ)+
      Real.log (Fintype.card (ScoredPayload U S.card σ (P η σ D R) τ):ℝ)≤
        100*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+P η σ D R) ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    let p₀ := finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
      (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/40) 10 R L₀ c t).map
        (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t))
    p₀ none≤Real.exp (-(Nat.card K:ℝ)) ∧
    (∀W,0<p₀ (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
      (9/40:ℝ)*X.card≤(W∩X).card) := by
  sorry

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata FiniteEntropy ProjectiveRestriction ReverseCap
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end
