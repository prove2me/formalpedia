-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_scalarGenerating_coefficient
-- name    : OAI.DirectCrouzeix.Faber.scalarGenerating_coefficient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:43:57.501976+00:00
-- url     : https://prove2.me/theorems/76ceb0b2-e784-4cba-82ac-e2af84a7badf
-- title:
--   Generating function of the Faber polynomials of $\zeta\mapsto c\zeta+g(1/\zeta)$
-- statement:
--   Let $c\in\mathbb{C}$ with $c\neq0$ and let $g:\mathbb{C}\to\mathbb{C}$ be complex analytic at $0$. For a function $f$ analytic at $0$ let $\tau_k(f)=f^{(k)}(0)/k!$ denote its $k$-th Taylor coefficient at $0$. Define, for $u$ near $0$,
--   $$
--   L(u)=\frac{1}{c+u\,g(u)},\qquad W(u)=u\,L(u),\qquad N(u)=\big(c-u^2g'(u)\big)\,L(u),
--   $$
--   the polynomials
--   $$
--   \Phi_k(z)=\sum_{j=0}^{k}\tau_k\big(N\,W^j\big)\,z^j\qquad(k\in\mathbb{N}),
--   $$
--   and, for $z\in\mathbb{C}$, the function
--   $$
--   S_z(u)=\frac{c-u^2g'(u)}{c+u\,\big(g(u)-z\big)} .
--   $$
--   Then for every $z\in\mathbb{C}$ and every $k\in\mathbb{N}$
--   $$
--   \tau_k(S_z)=\Phi_k(z).
--   $$
--
--   Equivalently, $\sum_{k\ge0}\Phi_k(z)\,u^k$ is the Taylor series of $S_z$ at $u=0$. For $\psi(\zeta)=c\zeta+g(1/\zeta)$ and $u=1/\zeta$ one has $\psi'(\zeta)/(\psi(\zeta)-z)=u\,S_z(u)$, so the theorem is the classical generating relation
--   $$
--   \frac{\psi'(\zeta)}{\psi(\zeta)-z}=\sum_{k\ge0}\frac{\Phi_k(z)}{\zeta^{k+1}}
--   $$
--   of the Faber polynomials of $\psi$, stated at the level of Taylor coefficients. The explicit formula for $\Phi_k$ makes the polynomials concrete, while the generating function is what later computations, such as the expansion of $\Phi_k(\psi(1/v))$, work with.
--
--   **Formalization Note** $L$, $W$, $N$ are `localL c g`, `localW c g`, `localN c g`, $\Phi_k$ is `faberBasis c g k` (a `Polynomial ℂ` assembled from monomials) evaluated at $z$, and $S_z$ is `scalarGenerating c g z`. $\tau_k$ is `taylorCoeff`, defined via `iteratedDeriv` at $0$, and $g'$ is `deriv g`. These functions are total in Lean (division by $0$ returns $0$), but $\tau_k$ only depends on values near $0$, where $c+u\,g(u)$ and the denominator of $S_z$ are close to $c\neq0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/FaberPolynomials.lean#L95-L139

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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_106 u_107
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate

theorem OAI.DirectCrouzeix.Faber.scalarGenerating_coefficient {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (z : ℂ) (k : ℕ) :
    taylorCoeff (scalarGenerating c g z) k = (faberBasis c g k).eval z := by sorry
