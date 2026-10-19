-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_radialPower_halfLaplacian
-- name    : OAI.EuclideanRamsey.radialPower_halfLaplacian
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T01:57:54.990251+00:00
-- url     : https://prove2.me/theorems/74780543-d66e-4fca-828e-49f51ca96049
-- title:
--   Half-Laplacian of the radial power $(a+\|x\|^2)^p$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $n$ and let $e_1,\dots,e_n$ be an orthonormal basis of $E$. For a function $f:E\to\mathbb{R}$, its half-Laplacian at $x$ is
--   $$\tfrac12\Delta f(x)=\frac12\sum_{k=1}^nD^2f(x)[e_k,e_k],$$
--   where $D^2f(x)$ is the second Fréchet derivative of $f$ at $x$. For real numbers $a>0$ and $p$, let $\phi_{a,p}(x)=(a+\|x\|^2)^p$ be the radial power (a real power of the positive number $a+\|x\|^2$). Then for every $x\in E$
--   $$\tfrac12\Delta\phi_{a,p}(x)=p\,\bigl(a+\|x\|^2\bigr)^{p-2}\Bigl(n\,a+(n+2p-2)\,\|x\|^2\Bigr).$$
--
--   This explicit formula controls the sign of the Laplacian of radial kernels. For the exponent $p=\tfrac14-\tfrac n2<0$ one has $n+2p-2=-\tfrac32$, so $\tfrac12\Delta\phi_{a,p}(x)\ge0$ exactly when $\|x\|^2\ge\tfrac{2n}{3}a$; this is the input for building smooth compactly supported radial bumps whose Laplacian has a small weighted negative part.
--
--   **Formalization Note** `halfLaplacian f x` is `(1/2) * ∑ i, iteratedFDeriv ℝ 2 f x ![e i, e i]` with `e = stdOrthonormalBasis ℝ E`, and `radialPower a p x = (a + ‖x‖^2) ^ p` uses `Real.rpow`. No condition on $p$ is needed; $a>0$ keeps the base positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/SmoothingKernel.lean#L149-L174

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel

open OAI OAI.EuclideanRamsey
universe uDomain
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
variable {E : Type uDomain} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem OAI.EuclideanRamsey.radialPower_halfLaplacian {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    halfLaplacian (radialPower a p) x =
      p * (a+‖x‖^2)^(p-2) *
        ((Module.finrank ℝ E : ℝ)*a + (Module.finrank ℝ E + 2*p-2)*‖x‖^2) := by sorry
