-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_eventually_reciprocal_coded_stage
-- name    : OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:03:09.824288+00:00
-- url     : https://prove2.me/theorems/350a6af0-d7aa-417c-863b-a27b953e3f20
-- title:
--   OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage` of [lean/OAI/Combinatorics/RamseyFive/Marking/ReciprocalSharpRound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/ReciprocalSharpRound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.SelectedTuple`, with `open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree ReverseCap ScoreGeometry`, `open ParameterHierarchy Filter`, `open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal`):
--
--   ```lean
--   theorem eventually_reciprocal_coded_stage {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D k J lo hi B M width : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [CharP K q₀] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
--       ∀ (_hd : finrank K V=5) (_hq3 : 3≤Nat.card K) (N w n H rounds rem l : ℕ) [Nonempty (Fin n)]
--         (admissible : (Fin N→α)→Prop)
--         (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
--         (ctx : Ω→κ) (PS : Prepared S ctx J B M)
--         (u : κ→Slots w n→ℝ) (b : Fin 7)
--         (_hforward : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,ForwardCaps (PS.domain c (slotEmbedding i)) (u c i))
--         (_hflag : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,((PS.domain c (slotEmbedding i)).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
--         (_hu : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,lo≤u c i ∧ u c i≤hi)
--         (_hband : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,BandCondition (Real.log (Nat.card K)) width (u c i) b)
--         (_hlohi : lo≤hi) (_hk : 0<k) (_hJ : 4*Real.log (Nat.card K)≤J)
--         (_hσ : 1≤σ) (_hq : Real.exp σ=Nat.card K),
--         Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
--         0 < rounds → 0 < rem → n≤2*rem → rem+rounds≤n → l<w*(2*n) →
--         0≤M → 2≤D*σ^(2*beta η) →
--         Real.log 32+width+3*(D*σ^(2*beta η))<Real.log (Nat.card K) →
--         Real.log 32+3*(D*σ^(2*beta η))<width →
--         0≤k+2*(D*σ^(2*beta η))+Real.log 4 →
--         k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η) →
--         w<2^H → (H:ℝ)≤σ^beta η →
--         reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2 →
--         2*(D*σ^beta η+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/(D*σ^(2*beta η))+
--           2*Real.exp 1*reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2 →
--         ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*(Nat.card K:ℝ)) →
--         5*(B/(D*σ^beta η)+(2*B/rounds+(if b.val%2=0 then (4*(w*(4*n):ℝ)*M)/rem else 0))/(σ^(-2000*beta η)/Real.exp σ))+
--           (2*n:ℝ)*((hi-lo+2*(w:ℝ)*(2*(D*σ^(2*beta η))+Real.log 64))/k)+(w*(2*n):ℝ)*ρ≤
--           ((w*(2*n):ℝ)-l)/10 →
--         Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
--           (windowCodeBudget σ (Nat.card K) (P η σ D R) (k+2*(D*σ^(2*beta η))+Real.log 4) w H+
--             (w+1)*Real.log (l+1)) (4*σ+codeDomainSlack k (D*σ^(2*beta η))) M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.map`, `OAI.SharpRamseyFive.Marking.FlagPair`, `OAI.SharpRamseyFive.SelectedTuple.CodedStream`, `OAI.SharpRamseyFive.SelectedTuple.SelectedStream`, `OAI.SharpRamseyFive.Windows.Slots` and `OAI.SharpRamseyFive.FiniteEntropy.Law` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.Marking.BandCondition`, `OAI.SharpRamseyFive.Marking.codeDomainSlack`, `OAI.SharpRamseyFive.Marking.reciprocalBadMass`, `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range`, `OAI.SharpRamseyFive.ParameterHierarchy.beta` and `OAI.SharpRamseyFive.ProjectiveIncidence.windowCodeBudget` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.Marking.ForwardCaps`, `OAI.SharpRamseyFive.SelectedTuple.Prepared` and `OAI.SharpRamseyFive.Windows.slotEmbedding` (definitions bundle `OAIQ060R002` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/ReciprocalSharpRound.lean (declaration OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage)

import Mathlib
import Definitions.Def_OAIQ060R002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree ReverseCap ScoreGeometry
open ParameterHierarchy Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal
noncomputable section

theorem eventually_reciprocal_coded_stage {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k J lo hi B M width : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
    ∀ (_hd : finrank K V=5) (_hq3 : 3≤Nat.card K) (N w n H rounds rem l : ℕ) [Nonempty (Fin n)]
      (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
      (ctx : Ω→κ) (PS : Prepared S ctx J B M)
      (u : κ→Slots w n→ℝ) (b : Fin 7)
      (_hforward : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,ForwardCaps (PS.domain c (slotEmbedding i)) (u c i))
      (_hflag : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,((PS.domain c (slotEmbedding i)).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
      (_hu : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,lo≤u c i ∧ u c i≤hi)
      (_hband : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,BandCondition (Real.log (Nat.card K)) width (u c i) b)
      (_hlohi : lo≤hi) (_hk : 0<k) (_hJ : 4*Real.log (Nat.card K)≤J)
      (_hσ : 1≤σ) (_hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
      0 < rounds → 0 < rem → n≤2*rem → rem+rounds≤n → l<w*(2*n) →
      0≤M → 2≤D*σ^(2*beta η) →
      Real.log 32+width+3*(D*σ^(2*beta η))<Real.log (Nat.card K) →
      Real.log 32+3*(D*σ^(2*beta η))<width →
      0≤k+2*(D*σ^(2*beta η))+Real.log 4 →
      k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η) →
      w<2^H → (H:ℝ)≤σ^beta η →
      reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2 →
      2*(D*σ^beta η+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/(D*σ^(2*beta η))+
        2*Real.exp 1*reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2 →
      ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*(Nat.card K:ℝ)) →
      5*(B/(D*σ^beta η)+(2*B/rounds+(if b.val%2=0 then (4*(w*(4*n):ℝ)*M)/rem else 0))/(σ^(-2000*beta η)/Real.exp σ))+
        (2*n:ℝ)*((hi-lo+2*(w:ℝ)*(2*(D*σ^(2*beta η))+Real.log 64))/k)+(w*(2*n):ℝ)*ρ≤
        ((w*(2*n):ℝ)-l)/10 →
      Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
        (windowCodeBudget σ (Nat.card K) (P η σ D R) (k+2*(D*σ^(2*beta η))+Real.log 4) w H+
          (w+1)*Real.log (l+1)) (4*σ+codeDomainSlack k (D*σ^(2*beta η))) M) := by
  sorry
end

end SharpRamseyFive.SelectedTuple

end OAI
end
