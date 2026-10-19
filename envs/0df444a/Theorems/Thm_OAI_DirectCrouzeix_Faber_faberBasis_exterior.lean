-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_faberBasis_exterior
-- name    : OAI.DirectCrouzeix.Faber.faberBasis_exterior
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:45:21.916886+00:00
-- url     : https://prove2.me/theorems/0169e0f3-8548-4976-88db-45447efd8b34
-- title:
--   Faber polynomials at exterior points: $\Phi_k(\psi(1/v))=v^{-k}+\tau_k(K(\cdot,v))$
-- statement:
--   Let $R>0$, let $g:\mathbb{C}\to\mathbb{C}$ be complex analytic on the open disk $\mathbb{D}_R=\{u\in\mathbb{C}:|u|<R\}$, and let $c\in\mathbb{C}$ with $c\neq0$. We use the following notation.
--   - $\psi(\zeta)=c\,\zeta+g(1/\zeta)$ is the exterior map, and $\tau_k(f)=f^{(k)}(0)/k!$ is the $k$-th Taylor coefficient at $0$.
--   - $\Phi_k(z)=\sum_{j=0}^k\tau_k(N\,W^j)\,z^j$ are the Faber polynomials of $\psi$, where $L(u)=(c+u\,g(u))^{-1}$, $W(u)=u\,L(u)$ and $N(u)=(c-u^2g'(u))\,L(u)$.
--   - $D(u,v)=\int_0^1g'((1-t)u+tv)\,dt$, $D_L(u,v)=\int_0^1(1-t)\,g''((1-t)u+tv)\,dt$, $H(u,v)=c-uv\,D(u,v)$, and $K(u,v)=uv\,\big(D(u,v)+u\,D_L(u,v)\big)/H(u,v)$ is the correction kernel.
--
--   Let $v\in\mathbb{D}_R$ with $v\neq0$, and assume $H(u,v)\neq0$ for every $u\in\mathbb{D}_R$. Then for every $k\in\mathbb{N}$
--   $$
--   \Phi_k\big(\psi(1/v)\big)=v^{-k}+\tau_k\big(u\mapsto K(u,v)\big).
--   $$
--
--   With $\zeta=1/v$, a point with $|\zeta|>1/R$, the theorem reads $\Phi_k(\psi(\zeta))=\zeta^k+\tau_k\big(K(\cdot,1/\zeta)\big)$. So the Faber polynomial composed with $\psi$ is the pure power $\zeta^k$ plus an error term given explicitly as a Taylor coefficient of the kernel $K$, which is analytic in $u$ on $\mathbb{D}_R$ and vanishes for $v=0$; this matches the classical description of $\Phi_k\circ\psi$ as $\zeta^k$ plus terms in negative powers of $\zeta$. For $R>1$ and $v$ on the unit circle it expresses $\Phi_k$ along the curve $s\mapsto\psi(e^{2\pi is})$ as $e^{2\pi iks}$ plus a boundary error term.
--
--   **Formalization Note** The left side is `(faberBasis c g k).eval (exterior c g v⁻¹)` and the error term is `taylorCoeff (fun u => correction c g u v) k`; $\mathbb{D}_R$ is `ball 0 R` and analyticity is `AnalyticOnNhd ℂ g (ball 0 R)`. The hypothesis on $H$ at $u=0$ already gives $H(0,v)=c\neq0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/FaberPolynomials.lean#L158-L177

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

theorem OAI.DirectCrouzeix.Faber.faberBasis_exterior {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    {v : ℂ} (hv : v ∈ ball 0 R) (hv0 : v ≠ 0)
    (hH : ∀ u ∈ ball 0 R, chordDenominator c g u v ≠ 0) (k : ℕ) :
    (faberBasis c g k).eval (exterior c g v⁻¹) = v⁻¹^k +
      taylorCoeff (fun u => correction c g u v) k := by sorry
