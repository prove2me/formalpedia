-- Prove2me | Theorems.Thm_OAI_QuarticPowerFree_physical_affine_count
-- name    : OAI.QuarticPowerFree.physical_affine_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T15:06:38.710758+00:00
-- url     : https://prove2.me/theorems/a41a748a-411c-475f-a3d1-fae49d6ebb88
-- title:
--   OAI.QuarticPowerFree.physical_affine_count: intermediate lemma from OpenAI, Squarefree values of quartics and power-free values of polynomials
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.QuarticPowerFree.allDegrees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Squarefree values of quartics and power-free values of polynomials*, OpenAI Math Release, September 24, 2026, result family 20, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.QuarticPowerFree.physical_affine_count` of [lean/OAI/NumberTheory/PowerFree/AffineCounting.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/AffineCounting.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.QuarticPowerFree`, with `open scoped BigOperators`, `open Matrix`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open MvPolynomial`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem physical_affine_count (n r A e₀ : ℕ) (hr : 0 < r)
--       (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (Cbox w : ℝ) (hCbox : 1 ≤ Cbox) (hw : 0 ≤ w)
--       (a δ : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hδ : ∀ i, 0 < δ i)
--       (hprefix : ∀ i, δ i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), a j)
--       (ε : ℝ) (hε : 0 < ε) (c Kex : ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) (hKex : ∀ e, 1 ≤ Kex e) :
--       ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X →
--         ∀ (G : KernelGeometry n), G.height ≤ X^w →
--           (∀ z ∈ G.points, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
--         ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime →
--           affineDimension I ≤ r → affineDegree I ≤ e₀ →
--           (∀ z ∈ G.points, PointOn I z) →
--           (∀ (i : Fin r) (e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
--             I ≤ J → EquationLock J G.points A → affineDegree J ≤ e →
--             affineDimension J = r-i.val → (∃ z ∈ G.points, PointOn J z) →
--             ((G.points.filter (PointOn J)).card:ℝ) ≤ Kex e*X^(ε/4) ∨
--             ∀ T : ℝ, 1 ≤ T → T^(r-i.val) / (((r-i.val).factorial:ℝ)*(δ i)^(r-i.val)) -
--               c e*T^(r-i.val-1) ≤ weightedHilbert J ω T) →
--           (G.points.card:ℝ) ≤ C*X^((∑ i, ((r-i.val:ℕ):ℝ)*a i)+ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.QuarticPowerFree.EquationLock`, `OAI.QuarticPowerFree.KernelGeometry`, `OAI.QuarticPowerFree.PointOn`, `OAI.QuarticPowerFree.affineDegree`, `OAI.QuarticPowerFree.affineDimension` and `OAI.QuarticPowerFree.weightedHilbert` (definitions bundle `OAIB3Qp000` of this split).
--
--   **Used by.** The proofs of `OAI.QuarticPowerFree.allDegrees`, `OAI.QuarticPowerFree.medium_degree_dyadic_tail` and `OAI.QuarticPowerFree.quartic_dyadic_tail` of this split import it.
-- source:
--   OpenAI, Squarefree values of quartics and power-free values of polynomials, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 20; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/AffineCounting.lean (declaration OAI.QuarticPowerFree.physical_affine_count)

import Mathlib
import Definitions.Def_OAIB3Qp000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open scoped BigOperators

open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_affine_count (n r A e₀ : ℕ) (hr : 0 < r)
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (Cbox w : ℝ) (hCbox : 1 ≤ Cbox) (hw : 0 ≤ w)
    (a δ : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hδ : ∀ i, 0 < δ i)
    (hprefix : ∀ i, δ i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), a j)
    (ε : ℝ) (hε : 0 < ε) (c Kex : ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) (hKex : ∀ e, 1 ≤ Kex e) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X →
      ∀ (G : KernelGeometry n), G.height ≤ X^w →
        (∀ z ∈ G.points, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime →
        affineDimension I ≤ r → affineDegree I ≤ e₀ →
        (∀ z ∈ G.points, PointOn I z) →
        (∀ (i : Fin r) (e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
          I ≤ J → EquationLock J G.points A → affineDegree J ≤ e →
          affineDimension J = r-i.val → (∃ z ∈ G.points, PointOn J z) →
          ((G.points.filter (PointOn J)).card:ℝ) ≤ Kex e*X^(ε/4) ∨
          ∀ T : ℝ, 1 ≤ T → T^(r-i.val) / (((r-i.val).factorial:ℝ)*(δ i)^(r-i.val)) -
            c e*T^(r-i.val-1) ≤ weightedHilbert J ω T) →
        (G.points.card:ℝ) ≤ C*X^((∑ i, ((r-i.val:ℕ):ℝ)*a i)+ε) := by
  sorry

end QuarticPowerFree

end OAI
end
