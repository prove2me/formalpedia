-- Prove2me | Theorems.Thm_MeasureTheory_eLpNorm_sub_convolution_le_of_support
-- name    : MeasureTheory.eLpNorm_sub_convolution_le_of_support
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:18:09.560001+00:00
-- url     : https://prove2.me/theorems/2fd4adf8-8c05-4960-8c75-b81ff58cad5c
-- title:
--   Convolution error bounded by translation errors on the kernel support
-- statement:
--   Let $n\ge0$, $1\le p<\infty$, and $d\in L^p(\mathbb R^n)$, with Lebesgue measure. Let $\rho:\mathbb R^n\to\mathbb R$ be continuous, compactly supported, nonnegative, and normalized by $\int\rho=1$. For any extended nonnegative bound $\varepsilon$, suppose that
--
--   $$\|d(\cdot-y)-d\|_{L^p}\le\varepsilon\qquad(y\in\operatorname{supp}\rho).$$
--
--   Then
--
--   $$\|d-\rho*d\|_{L^p}\le\varepsilon.$$
--
--   Here support means the set where the kernel is nonzero, and convolution is $\rho*d(x)=\int\rho(y)d(x-y)\,dy$. This quantitative averaging estimate applies to arbitrary probability kernels of compact support, without radiality or smoothness. It isolates the convolution estimate needed for approximate identities and mollification. Dimension zero and an infinite bound are included.
-- source:
--   Derived quantitative averaging estimate underlying John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Theorem 1.7 (Jensen inequality, printed p. 4), Theorem 1.23 (Young inequality, printed p. 9), Theorem 1.28 and its proof (printed p. 12). The displayed translation-error bound is a derived corollary of Minkowski/Jensen and the mass-one normalization, not a verbatim statement in Hunter. Related independently Proved p=2 interface: BookProof.MollifierL2.eLpNorm_mollify_sub_le (7e672305-1e03-43e5-84d0-b06518b04edb).

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ContinuousLinearMap
open scoped Convolution

theorem MeasureTheory.eLpNorm_sub_convolution_le_of_support {n : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1)
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hd : MemLp d p volume)
    (ε : ENNReal)
    (hε : ∀ y ∈ Function.support ρ,
      eLpNorm (fun x => d (x - y) - d x) p volume ≤ ε) :
    eLpNorm (d - (ρ ⋆[lsmul ℝ ℝ, volume] d)) p volume ≤ ε := by sorry
