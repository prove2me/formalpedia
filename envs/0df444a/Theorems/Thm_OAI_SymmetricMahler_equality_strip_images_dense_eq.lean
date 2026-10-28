-- Prove2me | Theorems.Thm_OAI_SymmetricMahler_equality_strip_images_dense_eq
-- name    : OAI.SymmetricMahler.equality_strip_images_dense_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:23:21.985987+00:00
-- url     : https://prove2.me/theorems/94049c5d-6d8b-463f-a2b7-5c28a58c29c8
-- title:
--   OAI.SymmetricMahler.equality_strip_images_dense_eq: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler_equality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SymmetricMahler.equality_strip_images_dense` of [lean/OAI/Analysis/Mahler/Mahler/Lens.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/Lens.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SymmetricMahler`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ENNReal`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ENNReal Pointwise`):
--
--   ```lean
--   theorem equality_strip_images_dense_eq {n : ℕ} (hn : 1 ≤ n)
--       {B : Set (Fin n → ℝ)} (hB : IsCompact B) (hconv : Convex ℝ B)
--       (hsym : ∀ x ∈ B, -x ∈ B) (hint : (interior B).Nonempty)
--       (heq : (volume B).toReal * (volume (coordinatePolar B)).toReal =
--         (4:ℝ)^n/(Nat.factorial n:ℝ))
--       (a : ℕ → coordinatePolar B)
--       (ha : ∀ j, Function.Injective (measurement (fun i : Fin (n+j) => (a i).val)))
--       (hcompact : ∀ j, IsCompact (stripBody (fun i : Fin (n+j) => (a i).val)))
--       (hsub : ∀ j, B ⊆ stripBody (fun i : Fin (n+j) => (a i).val))
--       (hvol : Tendsto (fun j => (volume (stripBody (fun i : Fin (n+j) => (a i).val))).toReal)
--         atTop (𝓝 (volume B).toReal))
--       (m : ℕ → ℕ) (hm : ∀ j, 2 ≤ m j)
--       (herr : Tendsto (fun j => ((n+j:ℕ):ℝ)*planarError (m j)) atTop (𝓝 0))
--       {x e : Fin n → ℝ} (hx : x ∈ B) (he : e ∈ coordinatePolar B) :
--       ∃ j : ℕ → ℕ, ∃ z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ)),
--         Tendsto j atTop atTop ∧
--         (∀ k, z k ∈ stripSublevel (fun i : Fin (n+j k) => (a i).val) (m (j k))) ∧
--         Tendsto (fun k => stripMap (fun i : Fin (n+j k) => (a i).val) (m (j k)) (z k))
--           atTop (𝓝 (x,e))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SymmetricMahler.measurement`, `OAI.SymmetricMahler.planarError`, `OAI.SymmetricMahler.stripBody`, `OAI.SymmetricMahler.stripMap` and `OAI.SymmetricMahler.stripSublevel` (definitions bundle `OAIQ2Ma000` of this split); `OAI.SymmetricMahler.coordinatePolar` (the published bundle `Def_SymmetricMahlerEquality`).
--
--   **Used by.** The proof of `OAI.SymmetricMahler.equality_polar_gauge_medians_eq` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/Lens.lean (declaration OAI.SymmetricMahler.equality_strip_images_dense)

import Mathlib
import Definitions.Def_SymmetricMahlerEquality
import Definitions.Def_OAIQ2Ma000

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace SymmetricMahler

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Pointwise

theorem equality_strip_images_dense_eq {n : ℕ} (hn : 1 ≤ n)
    {B : Set (Fin n → ℝ)} (hB : IsCompact B) (hconv : Convex ℝ B)
    (hsym : ∀ x ∈ B, -x ∈ B) (hint : (interior B).Nonempty)
    (heq : (volume B).toReal * (volume (coordinatePolar B)).toReal =
      (4:ℝ)^n/(Nat.factorial n:ℝ))
    (a : ℕ → coordinatePolar B)
    (ha : ∀ j, Function.Injective (measurement (fun i : Fin (n+j) => (a i).val)))
    (hcompact : ∀ j, IsCompact (stripBody (fun i : Fin (n+j) => (a i).val)))
    (hsub : ∀ j, B ⊆ stripBody (fun i : Fin (n+j) => (a i).val))
    (hvol : Tendsto (fun j => (volume (stripBody (fun i : Fin (n+j) => (a i).val))).toReal)
      atTop (𝓝 (volume B).toReal))
    (m : ℕ → ℕ) (hm : ∀ j, 2 ≤ m j)
    (herr : Tendsto (fun j => ((n+j:ℕ):ℝ)*planarError (m j)) atTop (𝓝 0))
    {x e : Fin n → ℝ} (hx : x ∈ B) (he : e ∈ coordinatePolar B) :
    ∃ j : ℕ → ℕ, ∃ z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ)),
      Tendsto j atTop atTop ∧
      (∀ k, z k ∈ stripSublevel (fun i : Fin (n+j k) => (a i).val) (m (j k))) ∧
      Tendsto (fun k => stripMap (fun i : Fin (n+j k) => (a i).val) (m (j k)) (z k))
        atTop (𝓝 (x,e)) := by
  sorry

end SymmetricMahler

open Set Filter Metric MeasureTheory Complex
open scoped Topology

open Set Filter
open scoped Topology

end

end OAI
end
