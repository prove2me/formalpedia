-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_memLp_affineOrthPart_408915f
-- name    : FunctionalInequalities.L2.memLp_affineOrthPart_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:31:27.882081+00:00
-- url     : https://prove2.me/theorems/4d9ecdb5-8291-41fe-8406-d3f43e056157
-- title:
--   Square Integrability of the Affine Residual
-- statement:
--   This statement asserts square integrability of the designated affine residual.
--
--   Let $n\in\mathbb N$, $E=$ `EuclideanSpace ℝ (Fin n)`, and $(e_j)$ its standard orthonormal basis. Let $\mu$ be a probability measure on $E$ with $\operatorname{id}\in L^2(\mu)$, and let $g:E\to\mathbb R$ belong to $L^2(\mu)$. Define $h=$ `L2.affineOrthPart μ g` by
--   $$
--   h(x)=g(x)-\int g\,d\mu-\sum_{j\in\operatorname{Fin}(n)}\left(\int\langle e_j,y\rangle g(y)\,d\mu(y)\right)\langle e_j,x\rangle.
--   $$
--   Then
--   $$
--   h\in L^2(\mu).
--   $$
--   This makes the residual available as an $L^2$ function in subsequent decomposition identities. No centering or identity-covariance assumption is required.
--
--   **Formalization Note** Membership is expressed by `MemLp`, including almost-everywhere strong measurability. All natural dimensions, including zero, are allowed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L244-L271 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.memLp_affineOrthPart`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section AffineOrthPart
variable {n : ℕ}

theorem FunctionalInequalities.L2.memLp_affineOrthPart_408915f (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    MemLp (affineOrthPart μ g) 2 μ := by sorry
