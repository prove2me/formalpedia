-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_producedPairLaw_spec
-- name    : OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:55:12.695069+00:00
-- url     : https://prove2.me/theorems/589b04c6-e90c-492d-bc13-13d95fccc055
-- title:
--   OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec` of [lean/OAI/Combinatorics/RamseyFive/Entropy/LocalNodeLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/LocalNodeLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ProjectiveIncidence`, with `open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy`, `open scoped Classical LinearAlgebra.Projectivization NNReal Topology`):
--
--   ```lean
--   lemma producedPairLaw_spec (hd : finrank K V=5) (hq : 3≤Nat.card K)
--       (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
--       (hA : A.Nonempty) (hB : B.Nonempty) (hAU : A⊆UA) (hBU : B⊆UB)
--       (c M : ℝ) (hc : 0 < c) (hc9 : c≤9/10)
--       (W : Finset (ℙ K V)) (hcap : CaptureBound A UA c M W)
--       (hsparse : 1000*(Nat.card K:ℝ)*incidences A B ≤ c*A.card*B.card) :
--       producedPairLaw A UA B UB hB c (some W) none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
--       ∀Y Z,0<producedPairLaw A UA B UB hB c (some W) (some (Y,Z))→
--         ValidCap B UB ((320/c+320)*(Nat.card K:ℝ)^5/A.card) (UB∩Y) ∧
--         ValidCap A UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card) (UA∩Z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.Law` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ReverseCap.CaptureBound` and `OAI.SharpRamseyFive.ReverseCap.ValidCap` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.incidences` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proofs of `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_guarded_node_cost` and `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_oriented_ready_encoded_failure` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Entropy/LocalNodeLaw.lean (declaration OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec)

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
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma producedPairLaw_spec (hd : finrank K V=5) (hq : 3≤Nat.card K)
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hAU : A⊆UA) (hBU : B⊆UB)
    (c M : ℝ) (hc : 0 < c) (hc9 : c≤9/10)
    (W : Finset (ℙ K V)) (hcap : CaptureBound A UA c M W)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B ≤ c*A.card*B.card) :
    producedPairLaw A UA B UB hB c (some W) none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
    ∀Y Z,0<producedPairLaw A UA B UB hB c (some W) (some (Y,Z))→
      ValidCap B UB ((320/c+320)*(Nat.card K:ℝ)^5/A.card) (UB∩Y) ∧
      ValidCap A UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card) (UA∩Z) := by
  sorry

end SharpRamseyFive.ProjectiveIncidence

end OAI
end
