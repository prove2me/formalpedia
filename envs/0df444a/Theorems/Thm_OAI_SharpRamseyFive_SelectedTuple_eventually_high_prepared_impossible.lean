-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_eventually_high_prepared_impossible
-- name    : OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:52:29.738594+00:00
-- url     : https://prove2.me/theorems/18768bc0-2d78-48d2-8ac6-410948612f35
-- title:
--   OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible` of [lean/OAI/Combinatorics/RamseyFive/Streams/SelectedLength.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Streams/SelectedLength.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.SelectedTuple`, with `open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples Filter ParameterHierarchy`, `open scoped Classical BigOperators LinearAlgebra.Projectivization`):
--
--   ```lean
--   theorem eventually_high_prepared_impossible {η : ℝ} (hη : 0<η) (c C Cb : ℝ)
--       (hc : 0 < c) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
--         [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
--       ∀ (N n r' : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
--         (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
--         (ctx : Ω→κ) (D J B M : ℝ) (P : Prepared S ctx J B M),
--         finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
--         7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
--         c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
--         σ^beta η≤D→D≤σ^(1-η/2)→B≤Cb*n*D*σ^(-beta η)→4*σ≤J→
--         2 ≤ r' → r' ≤ 4→(∀a,0 < map S.law ctx a→∀i,HighCaps (P.domain a i) 4 r')→False
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.map`, `OAI.SharpRamseyFive.Marking.FlagPair`, `OAI.SharpRamseyFive.SelectedTuple.SelectedStream` and `OAI.SharpRamseyFive.FiniteEntropy.Law` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.beta` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.Marking.HighCaps` and `OAI.SharpRamseyFive.SelectedTuple.Prepared` (definitions bundle `OAIQ060R002` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.SelectedTuple.eventually_prepared_dispatch` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Streams/SelectedLength.lean (declaration OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible)

import Mathlib
import Definitions.Def_OAIQ060R002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

theorem eventually_high_prepared_impossible {η : ℝ} (hη : 0<η) (c C Cb : ℝ)
    (hc : 0 < c) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
      [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
    ∀ (N n r' : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
      (ctx : Ω→κ) (D J B M : ℝ) (P : Prepared S ctx J B M),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
      σ^beta η≤D→D≤σ^(1-η/2)→B≤Cb*n*D*σ^(-beta η)→4*σ≤J→
      2 ≤ r' → r' ≤ 4→(∀a,0 < map S.law ctx a→∀i,HighCaps (P.domain a i) 4 r')→False := by
  sorry
end

end SharpRamseyFive.SelectedTuple

end OAI
end
