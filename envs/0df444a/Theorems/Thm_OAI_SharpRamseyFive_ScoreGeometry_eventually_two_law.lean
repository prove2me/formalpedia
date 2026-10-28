-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_two_law
-- name    : OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:58:26.236089+00:00
-- url     : https://prove2.me/theorems/9f0d2a38-8a01-4d54-8078-26642b1fa2f5
-- title:
--   OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law` of [lean/OAI/Combinatorics/RamseyFive/Geometry/BaseSmallLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/BaseSmallLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ScoreGeometry`, with `open Module ProjectiveIncidence FiniteEntropy Filter ParameterHierarchy`, `open scoped Classical LinearAlgebra.Projectivization NNReal Topology`):
--
--   ```lean
--   theorem eventually_two_law {η : ℝ} (hη : 0<η) (hη' : η<1/10)
--       (Cb : ℝ) (hCb : 0≤Cb) :
--       ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
--       ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
--         [Finite K] [FiniteDimensional K V]
--         [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
--         [∀x : ℙ K V,Fintype (RadialLine x)],
--       ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
--         finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
--         Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
--         0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → S.card≤T.card →
--         (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
--         (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
--         baseCaptureLaw S U (P η σ D R) τ R L₀ none≤Real.exp (-(Nat.card K:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.ProjectiveIncidence.RadialLine` and `OAI.SharpRamseyFive.FiniteEntropy.Law` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ParameterHierarchy.L`, `OAI.SharpRamseyFive.ParameterHierarchy.P`, `OAI.SharpRamseyFive.ParameterHierarchy.Range` and `OAI.SharpRamseyFive.ParameterHierarchy.beta` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.incidences` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.ScoreGeometry.baseCaptureLaw` (definitions bundle `OAIQ060R003` of this split).
--
--   **Used by.** The proofs of `OAI_SharpRamseyFive_ProjectiveRestriction_eventually_plane_public` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_oriented` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/BaseSmallLaw.lean (declaration OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law)

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

open Module ProjectiveIncidence FiniteEntropy Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_two_law {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → S.card≤T.card →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      baseCaptureLaw S U (P η σ D R) τ R L₀ none≤Real.exp (-(Nat.card K:ℝ)) := by
  sorry

end SharpRamseyFive.ScoreGeometry

end OAI
end
