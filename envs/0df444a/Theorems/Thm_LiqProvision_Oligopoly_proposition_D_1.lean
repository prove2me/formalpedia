-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_proposition_D_1
-- name    : LiqProvision.Oligopoly.proposition_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:50.095828+00:00
-- url     : https://prove2.me/theorems/b29dd468-f9e3-454b-9682-64fd26eeff95
-- title:
--   Proposition D.1, pp. 33–34 — log-concave densities: log-concave F and F̄, exponential tails, unimodal right derivative
-- statement:
--   Let $f:\mathbb R\to(0,\infty)$ be a log-concave probability density, with distribution function $F(x)=\int_{-\infty}^x f(y)\,dy$ and survival function $\bar F(x)=\int_x^\infty f(y)\,dy$. Then:
--
--   1. $F$ and $\bar F$ are log-concave;
--   2. there are $C>0$ and $\varepsilon>0$ with
--   $$f(x)\le C\,e^{-\varepsilon|x|}\qquad\text{for all }x\in\mathbb R;$$
--   3. $f$ has a right derivative $f'$ at every point, and there is $x^*\in\mathbb R$ with $f'\ge0$ on $(-\infty,x^*)$ and $f'\le0$ on $[x^*,\infty)$.
--
--   These are the basic regularity facts about log-concave densities on which the analysis of the effective type rests.
--
--   **Formalization Note.** Generic statement: it uses no model objects. Densities are real functions; a probability density is positive, integrable, of total integral $1$, and log-concave means that $\log f$ is concave on $\mathbb R$. The page writes $\bar F(x)=\int_{-\infty}^x f$, a misprint for the survival function $\int_x^\infty f$ of p. 4; the statement uses $\int_x^\infty f$.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, pp. 33–34, Proposition D.1

import Mathlib

namespace LiqProvision.Oligopoly
theorem proposition_D_1 (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x)
    (hint : MeasureTheory.Integrable f) (hmass : ∫ x, f x = 1)
    (hlc : ConcaveOn ℝ Set.univ (fun x => Real.log (f x))) :
    (ConcaveOn ℝ Set.univ (fun x => Real.log (∫ y in Set.Iic x, f y)) ∧
      ConcaveOn ℝ Set.univ (fun x => Real.log (∫ y in Set.Ioi x, f y))) ∧
    (∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ x, f x ≤ C * Real.exp (-ε * |x|)) ∧
    (∃ f' : ℝ → ℝ, (∀ x, HasDerivWithinAt f (f' x) (Set.Ici x) x) ∧
      ∃ xs : ℝ, (∀ x < xs, 0 ≤ f' x) ∧ ∀ x, xs ≤ x → f' x ≤ 0) := by sorry
end LiqProvision.Oligopoly
