-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_localBlockModel_ray
-- name    : OAI.BorsukNine.Admissible.localBlockModel_ray
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:42:34.491385+00:00
-- url     : https://prove2.me/theorems/0f9a22c6-a356-4805-a884-cf624794ffa9
-- title:
--   OAI.BorsukNine.Admissible.localBlockModel_ray: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.localBlockModel_ray` of [lean/OAI/Geometry/Borsuk/MatrixGeometry/ModelRay.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/MatrixGeometry/ModelRay.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open Set MeasureTheory`, `open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace`):
--
--   ```lean
--   lemma Admissible.localBlockModel_ray {f : E → ι → ℝ} (hf : Admissible f)
--       {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
--       (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
--       {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
--       (D : W ≃L[ℝ] W) {A : M} (hA : IsSelfAdjoint A)
--       {y : ι → ℝ} {rho d : ℝ} (hr : 0 < rho) (hd : 0 < d)
--       (hyi : ∀ i ∈ I, y i = rho * f c i) (hyo : ∀ i ∉ I, y i ≤ 0)
--       (hM : localBlockModel f c e a D A = d • y) :
--       blockOff c e A = 0 ∧ 0 < blockScalar c A ∧
--       localBlockModel f c e a D A = signedExtension f A ∧
--       A⁺ = blockScalar c A • rankOne c
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.blockOff`, `OAI.BorsukNine.blockScalar`, `OAI.BorsukNine.localBlockModel`, `OAI.BorsukNine.positiveSupport`, `OAI.BorsukNine.rankOne` and `OAI.BorsukNine.signedExtension` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proof of `OAI.BorsukNine.Admissible.no_free_ridge` of this split imports it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/MatrixGeometry/ModelRay.lean (declaration OAI.BorsukNine.Admissible.localBlockModel_ray)

import Mathlib
import Definitions.Def_OAIQ058B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section ModelRay
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix ν ν ℝ
lemma Admissible.localBlockModel_ray {f : E → ι → ℝ} (hf : Admissible f)
    {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : W ≃L[ℝ] W) {A : M} (hA : IsSelfAdjoint A)
    {y : ι → ℝ} {rho d : ℝ} (hr : 0 < rho) (hd : 0 < d)
    (hyi : ∀ i ∈ I, y i = rho * f c i) (hyo : ∀ i ∉ I, y i ≤ 0)
    (hM : localBlockModel f c e a D A = d • y) :
    blockOff c e A = 0 ∧ 0 < blockScalar c A ∧
    localBlockModel f c e a D A = signedExtension f A ∧
    A⁺ = blockScalar c A • rankOne c := by
  sorry
end ModelRay
end BorsukNine

end OAI
end
