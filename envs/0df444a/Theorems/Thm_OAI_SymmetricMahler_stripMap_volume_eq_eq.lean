-- Prove2me | Theorems.Thm_OAI_SymmetricMahler_stripMap_volume_eq_eq
-- name    : OAI.SymmetricMahler.stripMap_volume_eq_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:24:10.848361+00:00
-- url     : https://prove2.me/theorems/57913e68-cfbd-4951-849f-c811ca98b1ae
-- title:
--   OAI.SymmetricMahler.stripMap_volume_eq_eq: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler_equality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SymmetricMahler.stripMap_volume_eq` of [lean/OAI/Analysis/Mahler/Mahler/StripVolume.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/StripVolume.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SymmetricMahler`, with `open Real Complex Set Finset MeasureTheory`, `open scoped Topology ENNReal Pointwise`, `open MahlerConformal`):
--
--   ```lean
--   theorem stripMap_volume_eq_eq (A : Matrix (Fin N) (Fin n) ℝ)
--       (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 2 ≤ m) :
--       volume (stripMap A m '' stripSublevel A m) =
--         ∫⁻ z in stripSublevel A m,
--           ENNReal.ofReal ((4/(Real.pi*(m : ℝ)))^n*stripHessianDet A m z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SymmetricMahler.measurement`, `OAI.SymmetricMahler.stripHessianDet`, `OAI.SymmetricMahler.stripMap` and `OAI.SymmetricMahler.stripSublevel` (definitions bundle `OAIQ2Ma000` of this split).
--
--   **Used by.** The proof of `OAI.SymmetricMahler.equality_strip_images_dense_eq` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/StripVolume.lean (declaration OAI.SymmetricMahler.stripMap_volume_eq)

import Mathlib
import Definitions.Def_OAIQ2Ma000

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology ENNReal Pointwise
open MahlerConformal
variable {n N : ℕ}

theorem stripMap_volume_eq_eq (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 2 ≤ m) :
    volume (stripMap A m '' stripSublevel A m) =
      ∫⁻ z in stripSublevel A m,
        ENNReal.ofReal ((4/(Real.pi*(m : ℝ)))^n*stripHessianDet A m z) := by
  sorry

end SymmetricMahler

end OAI
end
