-- Prove2me | Theorems.Thm_OAI_QuarticPowerFree_quartic_surface_alternatives
-- name    : OAI.QuarticPowerFree.quartic_surface_alternatives
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T15:07:17.166501+00:00
-- url     : https://prove2.me/theorems/efff790b-8fd7-46b8-a9bc-68379e7d5a85
-- title:
--   OAI.QuarticPowerFree.quartic_surface_alternatives: intermediate lemma from OpenAI, Squarefree values of quartics and power-free values of polynomials
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.QuarticPowerFree.allDegrees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Squarefree values of quartics and power-free values of polynomials*, OpenAI Math Release, September 24, 2026, result family 20, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.QuarticPowerFree.quartic_surface_alternatives` of [lean/OAI/NumberTheory/PowerFree/QuarticSurfaces.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/QuarticSurfaces.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.QuarticPowerFree`, with `open MvPolynomial`, `open MvPolynomial`, `open scoped Classical`):
--
--   ```lean
--   theorem quartic_surface_alternatives {n D A B : ℕ} (hD : 0 < D)
--       (U V L : ℝ) (hU : 0 < U) (hV : 0 < V) (hL : 0 < L)
--       (hA : (A:ℝ)=L*U) (hB : (B:ℝ)=L*V)
--       (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0)
--       (hscale : ∀ i, (w i:ℝ)=L*ω i) (M : QuarticBoxSystem n D A B U ω w) (E : ℕ) :
--       ∃ H : ℝ, 0 ≤ H ∧ ∀ (S : Finset (Fin n → ℤ)) (F R : ℕ),
--       (∀ c : Fin 4 → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
--       (∀ z₀ ∈ S, (S.filter (fun z => ∃ c : ℂ, ∀ i,
--         MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i)=c*MvPolynomial.aeval (fun j => (z₀ j:ℂ)) (M.a i))).card ≤ R) →
--       (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
--       ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
--       (∀ z ∈ S, PointOn I z) →
--       (∀ i, Ideal.Quotient.mk I (M.a i) ≠ 0) →
--       Transcendental ℂ (Ideal.Quotient.mk I M.q) → affineDimension I = 2 → affineDegree I ≤ E →
--       S.card ≤ F+R ∨ ∀ T : ℝ, 1 ≤ T →
--         min (((min (2*A) B:ℕ):ℝ)*((2*A+B:ℕ):ℝ)*L^2/(2*(A:ℝ)^2*(B:ℝ)^2))
--           ((V+4*U)/(2*U*V^2))*T^2-H*T ≤ weightedHilbert I ω T
--   ```
--
--   **Definitions.** The statement is written with `OAI.QuarticPowerFree.PointOn`, `OAI.QuarticPowerFree.QuarticBoxSystem`, `OAI.QuarticPowerFree.affineDegree`, `OAI.QuarticPowerFree.affineDimension`, `OAI.QuarticPowerFree.weightedHilbert`, `OAI.QuarticPowerFree.QuarticBoxSystem.a` and `OAI.QuarticPowerFree.QuarticBoxSystem.ideal` (definitions bundle `OAIB3Qp000` of this split).
--
--   **Used by.** The proof of `OAI.QuarticPowerFree.quartic_dyadic_tail` of this split imports it.
-- source:
--   OpenAI, Squarefree values of quartics and power-free values of polynomials, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 20; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PowerFree/QuarticSurfaces.lean (declaration OAI.QuarticPowerFree.quartic_surface_alternatives)

import Mathlib
import Definitions.Def_OAIB3Qp000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open MvPolynomial

open MvPolynomial
open scoped Classical

theorem quartic_surface_alternatives {n D A B : ℕ} (hD : 0 < D)
    (U V L : ℝ) (hU : 0 < U) (hV : 0 < V) (hL : 0 < L)
    (hA : (A:ℝ)=L*U) (hB : (B:ℝ)=L*V)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0)
    (hscale : ∀ i, (w i:ℝ)=L*ω i) (M : QuarticBoxSystem n D A B U ω w) (E : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (S : Finset (Fin n → ℤ)) (F R : ℕ),
    (∀ c : Fin 4 → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
    (∀ z₀ ∈ S, (S.filter (fun z => ∃ c : ℂ, ∀ i,
      MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i)=c*MvPolynomial.aeval (fun j => (z₀ j:ℂ)) (M.a i))).card ≤ R) →
    (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
    ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
    (∀ z ∈ S, PointOn I z) →
    (∀ i, Ideal.Quotient.mk I (M.a i) ≠ 0) →
    Transcendental ℂ (Ideal.Quotient.mk I M.q) → affineDimension I = 2 → affineDegree I ≤ E →
    S.card ≤ F+R ∨ ∀ T : ℝ, 1 ≤ T →
      min (((min (2*A) B:ℕ):ℝ)*((2*A+B:ℕ):ℝ)*L^2/(2*(A:ℝ)^2*(B:ℝ)^2))
        ((V+4*U)/(2*U*V^2))*T^2-H*T ≤ weightedHilbert I ω T := by
  sorry

end QuarticPowerFree

end OAI
end
