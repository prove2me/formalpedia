-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_chordDenominator_ne_zero
-- name    : OAI.DirectCrouzeix.Faber.chordDenominator_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:40:50.894637+00:00
-- url     : https://prove2.me/theorems/4b081f66-ba9d-4c6a-a9f8-539f29ca8d44
-- title:
--   Univalence of $\zeta\mapsto c\zeta+g(1/\zeta)$ makes the chord denominator $c-uv\,D_g(u,v)$ nonvanishing
-- statement:
--   Let $g:\mathbb{C}\to\mathbb{C}$ and $c\in\mathbb{C}$. Define
--   $$
--   D_g(u,v)=\int_0^1 g'\big((1-t)u+tv\big)\,dt,\qquad H(u,v)=c-uv\,D_g(u,v),\qquad \psi(\zeta)=c\,\zeta+g(1/\zeta).
--   $$
--   Thus $D_g$ is the divided difference of $g$ written as an integral along the segment from $u$ to $v$, and $\psi$ is the associated exterior map. Let $s\subseteq\mathbb{C}$ be convex, let $g$ be complex analytic at every point of $s$, assume $c\neq0$, and put $\Omega^*=\{\zeta\in\mathbb{C}:\zeta\neq0,\ 1/\zeta\in s\}$. Suppose that
--   1. $\psi$ is injective on $\Omega^*$, and
--   2. $\psi'(\zeta)\neq0$ for every $\zeta\in\Omega^*$.
--
--   Then
--   $$
--   H(u,v)\neq0\qquad\text{for all }u,v\in s .
--   $$
--
--   For nonzero $u\neq v$ in $s$ one has $H(u,v)=\frac{\psi(1/u)-\psi(1/v)}{1/u-1/v}$, and for nonzero $u\in s$ one has $H(u,u)=c-u^2g'(u)=\psi'(1/u)$. So $H$ is the divided difference of $\psi$ in the inverted coordinate, and the theorem converts univalence of the exterior map (with nonvanishing derivative) into nonvanishing of $H$ on $s\times s$. This nonvanishing is the standing hypothesis under which the correction kernel $uv\,(\cdots)/H(u,v)$ of the Faber expansion is analytic.
--
--   **Formalization Note** $H$ is `chordDenominator c g u v`, $D_g$ is `divided g`, $\psi$ is `exterior c g`, and $\psi'$ is Lean's `deriv (exterior c g)`; at points of $\Omega^*$ the map $\psi$ is differentiable, so this is the true derivative. The set $\Omega^*$ is written `Inv.inv ⁻¹' s \ {0}`; since Lean sets $0^{-1}=0$, the point $0$ is removed explicitly. Openness of $s$ is not assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/DividedDifferences.lean#L103-L121

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate

theorem OAI.DirectCrouzeix.Faber.chordDenominator_ne_zero {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c : ℂ} (hc : c ≠ 0)
    (hinj : InjOn (exterior c g) (Inv.inv ⁻¹' s \ {0}))
    (hd : ∀ ζ, ζ ≠ 0 → ζ⁻¹ ∈ s → deriv (exterior c g) ζ ≠ 0)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) : chordDenominator c g u v ≠ 0 := by sorry
