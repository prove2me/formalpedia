-- Prove2me | Theorems.Thm_GeomDL_Blueprint_linear_invariant_eq_comp_average
-- name    : GeomDL.Blueprint.linear_invariant_eq_comp_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:28.738412+00:00
-- url     : https://prove2.me/theorems/32e20b4d-8128-48e1-b11b-42e23600c66c
-- title:
--   §3.5, p. 27 — a linear G-invariant f satisfies f(x) = (1/μ(G))∫f(g.x)dμ(g) = f(Ax): it sees x only through its G-average
-- statement:
--   Let a group $\mathfrak G$ act on a finite domain $\Omega$, and on real signals $x : \Omega \to \mathbb R$ by $(\mathfrak g . x)(u) = x(\mathfrak g^{-1}u)$. Let $\mu$ be a finite, nonzero measure on $\mathfrak G$, and let $f : X(\Omega) \to Y$ be a linear map into a real Banach space $Y$ that is $\mathfrak G$-invariant, $f(\mathfrak g . x) = f(x)$ for all $\mathfrak g$ and $x$. Then for every signal $x$,
--   $$f(x) = \frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} f(\mathfrak g . x)\, \mathrm d\mu(\mathfrak g) = f\!\left( \frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} (\mathfrak g . x)\, \mathrm d\mu(\mathfrak g) \right) = f(Ax).$$
--
--   So a linear invariant function depends on its input only through the $\mathfrak G$-average $Ax$; for images and translations, only through the average colour. This is the book's argument that expressive invariant models need a non-linear element.
--
--   **Formalization Note** The book takes $\mu$ to be the Haar measure; the identity uses no invariance of $\mu$, only that $0 < \mu(\mathfrak G) < \infty$, so no invariance is assumed. The domain is finite (the book's side-note on p. 15: "in practice, one must always discretise to a finite grid"), which makes every linear $f$ continuous. Measurability: the inversion of $\mathfrak G$ and the action are measurable, and $\Omega$ carries the discrete σ-algebra; a finite group with the counting measure and a compact group with its Haar measure acting continuously both fit.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.5, display after "A simple initial observation ..." and the G-average Ax, p. 27; side-note p. 27 (Haar measure)

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

namespace GeomDL.Blueprint

open MeasureTheory

/-- Bronstein et al., §3.5, p. 27: if `f` is linear and `G`-invariant, then for all signals `x`,
`f(x) = (1/μ(G)) ∫_G f(g.x) dμ(g) = f((1/μ(G)) ∫_G (g.x) dμ(g))`, so `f` depends on `x` only
through the `G`-average `A x`. Signals are real functions on a finite domain `Ω`; `μ` is any
finite nonzero measure on `G` (no invariance of `μ` is needed for this identity). -/
theorem linear_invariant_eq_comp_average {G Ω Y : Type*} [Group G] [MulAction G Ω] [Fintype Ω]
    [MeasurableSpace G] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    [MeasurableInv G] [MeasurableSMul G Ω]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Measure G) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (f : (Ω → ℝ) →ₗ[ℝ] Y) (hf : IsInvariant (G := G) f) (x : Ω → ℝ) :
    f x = (μ Set.univ).toReal⁻¹ • ∫ g, f (act g x) ∂μ ∧
    f x = f (groupAverage μ x) := by sorry

end GeomDL.Blueprint
