-- Prove2me | Theorems.Thm_FuzzyExtractors_EditSketch_appendix_E_ratio_unique
-- name    : FuzzyExtractors.EditSketch.appendix_E_ratio_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:09.655491+00:00
-- url     : https://prove2.me/theorems/1d59198f-4c79-4ac8-836d-1a36492b41a6
-- title:
--   Appendix E — every low-degree solution of the key equation has $\omega'/\sigma' = \omega/\sigma$
-- statement:
--   Let $K$ be a finite field of characteristic $2$, $\delta \ge 1$, and $M \subseteq K^*$ with $|M| \le (\delta - 1)/2$; let $\sigma$, $\omega$ and $S$ be the error locator, error evaluator and syndrome polynomial of $M$. Suppose $\sigma'(z) \ne 0$ and $\omega'(z)$ are polynomials of degree at most $(\delta - 1)/2$ with
--   $$S(z)\,\sigma'(z) \equiv \omega'(z) \pmod{z^\delta}.$$
--   Then $\omega'(z)/\sigma'(z) = \omega(z)/\sigma(z)$, that is,
--   $$\omega(z)\,\sigma'(z) = \sigma(z)\,\omega'(z).$$
--
--   This is the uniqueness step of the decoding argument: any low-degree solution of the key equation determines the reduced fraction $\omega/\sigma$, hence the error locator $\sigma$ (the solution with constant term $1$ and coprime to $\omega$).
--
--   **Formalization Note.** The ratio identity is stated cross-multiplied. The paper writes $w'(z)$ for the second unknown polynomial; it is $\omega'$ (a misprint of the Greek letter, not the string $w'$). "Nonzero solution" is read as $\sigma' \ne 0$; given the congruence and the degree bounds, a solution with $\sigma' = 0$ forces $\omega' = 0$, so this is the same as asking the pair to be nonzero. The weight bound $|M| \le (\delta-1)/2$ is the standing assumption of Lemma E.1(2). The designed distance is positive; at $\delta=0$ the congruence modulo $z^0$ is vacuous and the conclusion can fail. Degree bounds use `natDegree` with integer division $(\delta - 1)/2$.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Appendix E, proof of Lemma E.1, p. 44

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace FuzzyExtractors.EditSketch

open Polynomial in
theorem appendix_E_ratio_unique {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (δ : ℕ) (hδ : 1 ≤ δ) (M : Finset Kˣ) (hM : M.card ≤ (δ - 1) / 2)
    (σ' ω' : K[X]) (hσ' : σ' ≠ 0)
    (hdegσ : σ'.natDegree ≤ (δ - 1) / 2) (hdegω : ω'.natDegree ≤ (δ - 1) / 2)
    (hcong : X ^ δ ∣ synPoly δ M * σ' - ω') :
    omega M * σ' = sigma M * ω' := by sorry

end FuzzyExtractors.EditSketch
