-- Prove2me | Theorems.Thm_MeasureTheory_integral_comp_div_I0i_haar
-- name    : MeasureTheory.integral_comp_div_I0i_haar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:36:00.754884+00:00
-- url     : https://prove2.me/theorems/5c59c053-3fb2-4548-965b-85f861d604e7
-- title:
--   Invariance of the Haar integral $\int_0^\infty f(y)\,dy/y$ under the inversion-with-scaling $y\mapsto a/y$
-- statement:
--   Let $f\colon\mathbb{R}\to\mathbb{K}$ be a function into a normed field (or more generally the scalar field of the development), and let $a>0$ be a real number. Then
--
--   $$\int_0^{\infty} f\!\left(\frac{a}{y}\right)\frac{dy}{y} \;=\; \int_0^{\infty} f(y)\,\frac{dy}{y}.$$
--
--   The measure $dy/y$ is the Haar measure of the multiplicative group $(0,\infty)$, and the map $y\mapsto a/y$ is the composition of the group inversion with a translation by $a$; both operations preserve the Haar measure, so the substitution leaves the integral unchanged. No integrability hypothesis is required: the equality is between Bochner integrals under a measure-preserving change of variables.
--
--   This is one of a small family of change-of-variables lemmas for the multiplicative Haar measure on $(0,\infty)$ that underpin the Mellin calculus in this development — in particular the symmetry of the multiplicative (Mellin) convolution $\int_0^\infty f(y)g(x/y)\,dy/y$ and the factorization of its Mellin transform.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L75-L83

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

theorem MeasureTheory.integral_comp_div_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by sorry
