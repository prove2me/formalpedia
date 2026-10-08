-- Prove2me | Theorems.Thm_IncProx_Cyclic_proposition1
-- name    : IncProx.Cyclic.proposition1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:10.331779+00:00
-- url     : https://prove2.me/theorems/e36812e9-a81a-40d0-8587-3a88acd105b9
-- title:
--   Proposition 1 — the proximal iteration is a projected subgradient step at $x_{k+1}$; inequality (16)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be a nonempty closed convex set and let $f:\mathbb R^n\to(-\infty,\infty]$ be a closed proper convex function such that $\mathrm{ri}(X)\cap\mathrm{ri}(\mathrm{dom}(f))\neq\emptyset$, where $\mathrm{dom}(f)=\{x: f(x)<\infty\}$ and $\mathrm{ri}$ denotes the relative interior. Let $x_k\in\mathbb R^n$, $\alpha_k>0$, and let $x_{k+1}$ be given by the proximal iteration
--   $$x_{k+1}=\arg\min_{x\in X}\Big\{f(x)+\frac1{2\alpha_k}\|x-x_k\|^2\Big\}.\qquad(14)$$
--   Then:
--
--   1. **(a)** there is a subgradient $\tilde\nabla f(x_{k+1})$ of $f$ at $x_{k+1}$ (that is, $f(x_{k+1})$ is finite and $f(y)\ge f(x_{k+1})+\tilde\nabla f(x_{k+1})'(y-x_{k+1})$ for all $y$) with $x_{k+1}=P_X\big(x_k-\alpha_k\tilde\nabla f(x_{k+1})\big)$ (15);
--   2. **(b)** for every $y\in X$,
--   $$\|x_{k+1}-y\|^2\le\|x_k-y\|^2-2\alpha_k\big(f(x_{k+1})-f(y)\big)-\|x_k-x_{k+1}\|^2\le\|x_k-y\|^2-2\alpha_k\big(f(x_{k+1})-f(y)\big).\qquad(16)$$
--
--   Part (a) shows that each proximal step of the incremental methods is a projected subgradient step with the subgradient taken at the new point; part (b) is the basic estimate the convergence analysis rests on.
--
--   **Formalization Note** "Closed proper convex" is the class $\Gamma_0$ of the referenced definition `MoreauProx.Characterization.GammaZero` (lower semicontinuous, never $-\infty$, not identically $+\infty$, convex epigraph), and subgradients of extended-real-valued functions are its `subgrad`; values live in `EReal`. "$x_{k+1}=\arg\min$" is read as "$x_{k+1}\in X$ minimizes the proximal objective over $X$", computed in `EReal`. Part (b) is stated for $y\in X$ with $f(y)<\infty$: for $y\notin\mathrm{dom}(f)$ the right-hand side of (16) is $+\infty$ and the inequality says nothing, so this loses nothing; $f(x_{k+1})$ is finite under the hypotheses, and both values enter as real numbers (`EReal.toReal`). The stray "$i=1,\dots,m$" printed next to (15) in the paper has no meaning for Proposition 1 and is not formalized. Relative interiors are Mathlib's `intrinsicInterior`. $P_X$ is the nearest-point predicate `IsProj` of `IncProx.Cyclic.Basic`.
-- source:
--   Bertsekas, Incremental Proximal Methods for Large Scale Convex Optimization, LIDS-P-2847 (rev. March 2011), p. 6, Proposition 1 (eqs. (14)–(16))

import Mathlib
import Definitions.Def_IncProx_Cyclic_Basic
import Definitions.Def_MoreauProx_Characterization_GammaZero

namespace IncProx.Cyclic

open MoreauProx.Characterization

/-- Proposition 1 (p. 6). For a nonempty closed convex `X`, a closed proper convex
`f : ℝⁿ → (−∞, ∞]` (`GammaZero f`) with `ri X ∩ ri (dom f) ≠ ∅`, where `dom f = {x | f x < ∞}`, a point
`xk` and a stepsize `a > 0`, let `xk1` be a minimizer over `X` of `f(x) + ‖x − xk‖² / (2a)` (14).
Then (a) `xk1 = P_X(xk − a g)` for some subgradient `g` of `f` at `xk1` (15), and (b) for every
`y ∈ X` with `f y < ∞`, inequality (16). -/
theorem proposition1 {n : ℕ} (X : Set (Vec n)) (hXne : X.Nonempty) (hXcl : IsClosed X)
    (hXcv : Convex ℝ X) (f : Vec n → EReal) (hf : GammaZero f)
    (hri : (intrinsicInterior ℝ X ∩ intrinsicInterior ℝ {x | f x < ⊤}).Nonempty)
    (xk xk1 : Vec n) (a : ℝ) (ha : 0 < a)
    (hmin : xk1 ∈ X ∧ ∀ x ∈ X,
      f xk1 + ((‖xk1 - xk‖ ^ 2 / (2 * a) : ℝ) : EReal) ≤ f x + ((‖x - xk‖ ^ 2 / (2 * a) : ℝ) : EReal)) :
    (∃ g : Vec n, g ∈ subgrad f xk1 ∧ IsProj X (xk - a • g) xk1) ∧
    (∀ y ∈ X, f y ≠ ⊤ →
      ‖xk1 - y‖ ^ 2 ≤
          ‖xk - y‖ ^ 2 - 2 * a * ((f xk1).toReal - (f y).toReal) - ‖xk - xk1‖ ^ 2 ∧
      ‖xk - y‖ ^ 2 - 2 * a * ((f xk1).toReal - (f y).toReal) - ‖xk - xk1‖ ^ 2 ≤
          ‖xk - y‖ ^ 2 - 2 * a * ((f xk1).toReal - (f y).toReal)) := by sorry

end IncProx.Cyclic
