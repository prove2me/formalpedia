-- Prove2me | Theorems.Thm_MartOT_Abs_lemma_7_5
-- name    : MartOT.Abs.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:17.808221+00:00
-- url     : https://prove2.me/theorems/5692b1e3-735a-432a-859b-ca82c6d339e3
-- title:
--   Lemma 7.5, pp. 43–44 — sign table of A − B as a function of x′ in the three cases y′ < x, y′ > x, y′ = x
-- statement:
--   Let $x,y^-,y^+,y'\in\mathbb R$ with $y^-<x<y^+$ and $y^-<y'<y^+$, and let $\lambda$ be the number with $\lambda y^++(1-\lambda)y^-=y'$. For $x'\in\mathbb R$ put
--
--   $$A(x')=\lambda|x-y^+|+(1-\lambda)|x-y^-|+|x'-y'|,\qquad B(x')=\lambda|x'-y^+|+(1-\lambda)|x'-y^-|+|x-y'|.$$
--
--   1. If $y'<x$, there is $x_0\in\,]y^-,y'[$ such that $A-B$ vanishes exactly at $x_0$ and $x$, is strictly positive outside $[x_0,x]$ and strictly negative on $]x_0,x[$.
--   2. If $y'>x$, there is $x_1\in\,]y',y^+[$ such that $A-B$ vanishes exactly at $x$ and $x_1$, is strictly positive outside $[x,x_1]$ and strictly negative on $]x,x_1[$.
--   3. If $y'=x$, then $A-B\ge0$ everywhere and $A-B$ vanishes exactly at $x$.
--
--   This is the elementary comparison behind the proofs of Theorems 7.3 and 7.4: $A$ and $B$ are the costs, for $c(x,y)=|y-x|$, of a three-point configuration and of its rerouting, so the sign of $A-B$ decides which reroutings are improvements.
--
--   **Formalization Note** $A$ and $B$ are given as functions of $x'$ by defining equations. "Vanishes exactly at" is an "if and only if" over all $x'\in\mathbb R$.
-- source:
--   arXiv:1208.1509v2, Lemma 7.5, pp. 43–44

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem lemma_7_5 (x ym yp y' l : ℝ) (hx : ym < x ∧ x < yp) (hy : ym < y' ∧ y' < yp)
    (hl : l * yp + (1 - l) * ym = y') (A B : ℝ → ℝ)
    (hA : ∀ x' : ℝ, A x' = l * |x - yp| + (1 - l) * |x - ym| + |x' - y'|)
    (hB : ∀ x' : ℝ, B x' = l * |x' - yp| + (1 - l) * |x' - ym| + |x - y'|) :
    (y' < x → ∃ x0 ∈ Set.Ioo ym y',
      (∀ x' : ℝ, A x' - B x' = 0 ↔ x' = x0 ∨ x' = x) ∧
      (∀ x' : ℝ, x' ∉ Set.Icc x0 x → 0 < A x' - B x') ∧
      (∀ x' ∈ Set.Ioo x0 x, A x' - B x' < 0)) ∧
    (x < y' → ∃ x1 ∈ Set.Ioo y' yp,
      (∀ x' : ℝ, A x' - B x' = 0 ↔ x' = x1 ∨ x' = x) ∧
      (∀ x' : ℝ, x' ∉ Set.Icc x x1 → 0 < A x' - B x') ∧
      (∀ x' ∈ Set.Ioo x x1, A x' - B x' < 0)) ∧
    (y' = x → (∀ x' : ℝ, 0 ≤ A x' - B x') ∧ (∀ x' : ℝ, A x' - B x' = 0 ↔ x' = x)) := by sorry

end MartOT.Abs
