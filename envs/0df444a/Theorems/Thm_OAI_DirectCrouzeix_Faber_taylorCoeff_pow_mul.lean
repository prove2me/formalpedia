-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_taylorCoeff_pow_mul
-- name    : OAI.DirectCrouzeix.Faber.taylorCoeff_pow_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:42:55.319047+00:00
-- url     : https://prove2.me/theorems/07d157c5-ca6e-4b12-8015-ea511ec8d0dd
-- title:
--   Taylor coefficients of $u^jf(u)$ are shifted Taylor coefficients of $f$
-- statement:
--   For a function $f:\mathbb{C}\to\mathbb{C}$ and $k\in\mathbb{N}$ let
--   $$
--   \tau_k(f)=\frac{f^{(k)}(0)}{k!}
--   $$
--   be its $k$-th Taylor coefficient at the origin, where $f^{(k)}$ is the $k$-th complex derivative. If $f$ is complex analytic at $0$, then for all $j,k\in\mathbb{N}$
--   $$
--   \tau_k\big(u\mapsto u^jf(u)\big)=\begin{cases}\tau_{k-j}(f),&j\le k,\\ 0,&j>k.\end{cases}
--   $$
--
--   In terms of power series, multiplication by $u^j$ shifts the coefficient sequence by $j$ places. The rule is used to discard remainder terms of the form $u^{k+1}T(u)$ when extracting a $k$-th Taylor coefficient, for instance in the computation of the generating function of Faber polynomials and of their leading coefficients.
--
--   **Formalization Note** $\tau_k(f)$ is `taylorCoeff f k`, defined as $(k!)^{-1}$ times `iteratedDeriv k f 0`. The case distinction is an `if j ≤ k then … else 0`, and $k-j$ is natural-number subtraction, which is exact in the branch $j\le k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/TaylorFourier.lean#L51-L75

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate

theorem OAI.DirectCrouzeix.Faber.taylorCoeff_pow_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (j k : ℕ) :
    taylorCoeff (fun u => u^j*f u) k = if j ≤ k then taylorCoeff f (k-j) else 0 := by sorry
