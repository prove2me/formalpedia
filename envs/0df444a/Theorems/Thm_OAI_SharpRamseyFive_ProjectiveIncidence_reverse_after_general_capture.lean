-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_reverse_after_general_capture
-- name    : OAI.SharpRamseyFive.ProjectiveIncidence.reverse_after_general_capture
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:55:31.408986+00:00
-- url     : https://prove2.me/theorems/ee9738a5-19da-4159-a769-4e64ea52a3c1
-- title:
--   OAI.SharpRamseyFive.ProjectiveIncidence.reverse_after_general_capture: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ProjectiveIncidence.reverse_after_general_capture` of [lean/OAI/Combinatorics/RamseyFive/Decoding/FreshPublicValidation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Decoding/FreshPublicValidation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ProjectiveIncidence`, with `open Module FiniteEntropy ReverseCap`, `open scoped Classical LinearAlgebra.Projectivization BigOperators`):
--
--   ```lean
--   theorem reverse_after_general_capture {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
--       (hq : 3≤Nat.card K) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
--       (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty) (c : ℝ) (hc : 0 < c) (hc1 : c≤1)
--       (MT ε : ℝ) (p : Law (Option (Finset (ℙ K (Dual K V)))))
--       (hp : p none≤ε) (hgood : ∀W,0<p (some W)→CaptureBound T UT c MT W)
--       (hsparse : 1000*(Nat.card K:ℝ)*incidences S T ≤ c*S.card*T.card)
--       (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card)≤n) :
--       let M := (320/c+320)*(Nat.card K:ℝ)^(d+1)/T.card
--       let out := optionCompose p (generalNextCapLaw S U T UT hT c hc n (Nat.card K) M MT)
--       out none≤ε+Real.exp (-(Nat.card K:ℝ)) ∧
--       (∀Z,0<out (some Z)→ValidCap S U M Z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.Law` and `OAI.SharpRamseyFive.FiniteEntropy.optionCompose` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ReverseCap.CaptureBound` and `OAI.SharpRamseyFive.ReverseCap.ValidCap` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.incidences` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.generalNextCapLaw` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Decoding/FreshPublicValidation.lean (declaration OAI.SharpRamseyFive.ProjectiveIncidence.reverse_after_general_capture)

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem reverse_after_general_capture {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty) (c : ℝ) (hc : 0 < c) (hc1 : c≤1)
    (MT ε : ℝ) (p : Law (Option (Finset (ℙ K (Dual K V)))))
    (hp : p none≤ε) (hgood : ∀W,0<p (some W)→CaptureBound T UT c MT W)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences S T ≤ c*S.card*T.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card)≤n) :
    let M := (320/c+320)*(Nat.card K:ℝ)^(d+1)/T.card
    let out := optionCompose p (generalNextCapLaw S U T UT hT c hc n (Nat.card K) M MT)
    out none≤ε+Real.exp (-(Nat.card K:ℝ)) ∧
    (∀Z,0<out (some Z)→ValidCap S U M Z) := by
  sorry

end SharpRamseyFive.ProjectiveIncidence

end OAI
end
