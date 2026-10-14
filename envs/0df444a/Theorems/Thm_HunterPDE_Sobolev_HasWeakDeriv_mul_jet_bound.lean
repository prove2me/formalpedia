-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_mul_jet_bound
-- name    : HunterPDE.Sobolev.HasWeakDeriv.mul_jet_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:36:00.328981+00:00
-- url     : https://prove2.me/theorems/e5fc63a3-3ae7-4ad0-864c-50c5b97d36e0
-- title:
--   Pointwise jet bound for higher weak derivatives of a smooth product
-- statement:
--   Let $n,k$ be nonnegative integers, let $f$ be a real function on $\mathbb R^n$, and suppose $d_\beta$ is a locally integrable weak derivative of $f$ for every multi-index $|\beta|\le k$. Let $\eta$ be smooth and let $A:\mathbb R^n\to[0,\infty)$ be any pointwise envelope satisfying $|D^\beta\eta(x)|\le A(x)$ for all these orders. For every $|\alpha|\le k$, there is a locally integrable weak derivative $g_\alpha$ of $\eta f$ such that
--
--   $$|g_\alpha(x)|\le 2^k A(x)\sum_{|\beta|\le k}|d_\beta(x)|\qquad\text{for every }x\in\mathbb R^n.$$
--
--   This statement provides an actual representative with a pointwise bound. The envelope need not be measurable or bounded. It supports localized and weighted Sobolev estimates independently of the choice of an integrability exponent. It includes dimension and order zero.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Propositions 3.16 and 3.17, printed p. 54. Quantitative consequence of the repeated weak product rule: the multi-index Leibniz coefficients have total mass 2^{|α|} ≤ 2^k. This envelope bound is derived from, rather than quoted verbatim from, the source.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.HasWeakDeriv.mul_jet_bound {n k : ℕ}
    (f η : EuclideanSpace ℝ (Fin n) → ℝ)
    (d : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ β, ∑ i, β i ≤ k → HasWeakDeriv Set.univ β f (d β))
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (A : EuclideanSpace ℝ (Fin n) → ℝ) (hA : ∀ x, 0 ≤ A x)
    (hbound : ∀ β, ∑ i, β i ≤ k → ∀ x, ‖iteratedPartial β η x‖ ≤ A x)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) :
    ∃ g, HasWeakDeriv Set.univ α (fun x => η x * f x) g ∧
      ∀ x, ‖g x‖ ≤ (2 : ℝ) ^ k * A x * ∑ β ∈ multiIndices n k, ‖d β x‖ := by sorry
