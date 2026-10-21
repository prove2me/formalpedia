-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_proposition_D_2
-- name    : LiqProvision.Oligopoly.proposition_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:49.367338+00:00
-- url     : https://prove2.me/theorems/2d3d59e0-ed5c-44be-b5fd-aed3eae28624
-- title:
--   Proposition D.2, p. 34 — convolutions of log-concave densities are log-concave, C¹, with derivative f′ ∗ g
-- statement:
--   Let $f,g:\mathbb R\to(0,\infty)$ be log-concave probability densities and let $f'$ be the right derivative of $f$. Write $(f*g)(x)=\int_{\mathbb R} f(x-y)g(y)\,dy$ and $\mathrm{id}\,g$ for $y\mapsto y\,g(y)$.
--
--   1. $f*g$ is a positive log-concave probability density, continuously differentiable, with bounded derivative
--   $$(f*g)'=f'*g .$$
--   2. $f*(\mathrm{id}\,g)$ is integrable and continuously differentiable, with bounded derivative $(f*(\mathrm{id}\,g))'=f'*(\mathrm{id}\,g)$.
--
--   Applied to the densities of $S$ and $-\gamma_c M$, this gives the regularity of the effective-type density $f$ and of the numerator of the conditional mean $g$.
--
--   **Formalization Note.** Generic statement: it uses no model objects. Densities are real functions; a probability density is positive, integrable, of total integral $1$, and log-concave means that $\log f$ is concave on $\mathbb R$. The second density is called $h$ in Lean. The right derivative $f'$ is a hypothesis-bound function: any $f'$ with $f'(x)$ the derivative of $f$ within $[x,\infty)$ at every $x$ (it exists by Proposition D.1(c) and is unique). Convolutions are written as explicit integrals.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 34, Proposition D.2

import Mathlib

namespace LiqProvision.Oligopoly
theorem proposition_D_2 (f h : ℝ → ℝ)
    (hfpos : ∀ x, 0 < f x) (hfint : MeasureTheory.Integrable f) (hfmass : ∫ x, f x = 1)
    (hflc : ConcaveOn ℝ Set.univ (fun x => Real.log (f x)))
    (hhpos : ∀ x, 0 < h x) (hhint : MeasureTheory.Integrable h) (hhmass : ∫ x, h x = 1)
    (hhlc : ConcaveOn ℝ Set.univ (fun x => Real.log (h x)))
    (f' : ℝ → ℝ) (hf' : ∀ x, HasDerivWithinAt f (f' x) (Set.Ici x) x) :
    ((∀ x, 0 < ∫ y, f (x - y) * h y) ∧
      MeasureTheory.Integrable (fun x => ∫ y, f (x - y) * h y) ∧
      ∫ x, (∫ y, f (x - y) * h y) = 1 ∧
      ConcaveOn ℝ Set.univ (fun x => Real.log (∫ y, f (x - y) * h y)) ∧
      ContDiff ℝ 1 (fun x => ∫ y, f (x - y) * h y) ∧
      (∃ B : ℝ, ∀ x, |deriv (fun x => ∫ y, f (x - y) * h y) x| ≤ B) ∧
      ∀ x, deriv (fun x => ∫ y, f (x - y) * h y) x = ∫ y, f' (x - y) * h y) ∧
    (MeasureTheory.Integrable (fun x => ∫ y, f (x - y) * (y * h y)) ∧
      ContDiff ℝ 1 (fun x => ∫ y, f (x - y) * (y * h y)) ∧
      (∃ B : ℝ, ∀ x, |deriv (fun x => ∫ y, f (x - y) * (y * h y)) x| ≤ B) ∧
      ∀ x, deriv (fun x => ∫ y, f (x - y) * (y * h y)) x = ∫ y, f' (x - y) * (y * h y)) := by sorry
end LiqProvision.Oligopoly
