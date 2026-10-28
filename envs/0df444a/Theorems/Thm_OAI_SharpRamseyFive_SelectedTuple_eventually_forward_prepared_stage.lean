-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_eventually_forward_prepared_stage
-- name    : OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:52:39.096653+00:00
-- url     : https://prove2.me/theorems/374696c9-96a8-4e49-b09a-3539aabaf8a0
-- title:
--   OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage` of [lean/OAI/Combinatorics/RamseyFive/Iteration/ForwardPreparedStage.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Iteration/ForwardPreparedStage.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.SelectedTuple`, with `open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy`, `open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal`):
--
--   ```lean
--   theorem eventually_forward_prepared_stage {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (c C Cm : ℝ) (hc : 0 < c) (hC : 0≤C) (hCm : 0≤Cm) :
--       ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [CharP K q₀] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
--       ∀ (N m l : ℕ) (admissible : (Fin N→α)→Prop)
--         (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N m admissible)
--         (ctx : Ω→κ) (D B M k₀ : ℝ)
--         (PS : Prepared S ctx (Real.log (153*(Nat.card K:ℝ)^4)) B M) (b : Fin 7),
--         finrank K V=5→3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
--         σ^beta η≤D→D≤σ^(1-η/2)→c*(Nat.card K:ℝ)*σ^(1+η)≤ m→
--         (m:ℝ)≤(Nat.card K:ℝ)*σ^(1+η)→(l:ℝ)≤ m/100→
--         (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤B→B≤C*m*D*σ^(-beta η)→0≤M→M≤Cm*σ→
--         (∀a,0 < map S.law ctx a→∀i,DomainClass (D*σ^(3*beta η)) (PS.domain a i) (.inl b))→
--         Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
--           (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.map`, `OAI.SharpRamseyFive.Marking.FlagPair`, `OAI.SharpRamseyFive.SelectedTuple.CodedStream`, `OAI.SharpRamseyFive.SelectedTuple.SelectedStream` and `OAI.SharpRamseyFive.FiniteEntropy.Law` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.beta` and `OAI.SharpRamseyFive.ParameterHierarchy.domainSlackConstant` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.Marking.DomainClass` and `OAI.SharpRamseyFive.SelectedTuple.Prepared` (definitions bundle `OAIQ060R002` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.SelectedTuple.eventually_prepared_dispatch` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Iteration/ForwardPreparedStage.lean (declaration OAI.SharpRamseyFive.SelectedTuple.eventually_forward_prepared_stage)

import Mathlib
import Definitions.Def_OAIQ060R002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
noncomputable section

theorem eventually_forward_prepared_stage {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c C Cm : ℝ) (hc : 0 < c) (hC : 0≤C) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
    ∀ (N m l : ℕ) (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N m admissible)
      (ctx : Ω→κ) (D B M k₀ : ℝ)
      (PS : Prepared S ctx (Real.log (153*(Nat.card K:ℝ)^4)) B M) (b : Fin 7),
      finrank K V=5→3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      σ^beta η≤D→D≤σ^(1-η/2)→c*(Nat.card K:ℝ)*σ^(1+η)≤ m→
      (m:ℝ)≤(Nat.card K:ℝ)*σ^(1+η)→(l:ℝ)≤ m/100→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤B→B≤C*m*D*σ^(-beta η)→0≤M→M≤Cm*σ→
      (∀a,0 < map S.law ctx a→∀i,DomainClass (D*σ^(3*beta η)) (PS.domain a i) (.inl b))→
      Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) := by
  sorry
end
end SharpRamseyFive.SelectedTuple

end OAI
end
