-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_chordIntegral_deriv_mul
-- name    : OAI.DirectCrouzeix.Faber.chordIntegral_deriv_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:36:35.349385+00:00
-- url     : https://prove2.me/theorems/8a04988f-bd82-4e41-9694-f3cbbf0c10ea
-- title:
--   Fundamental theorem of calculus along a segment: $\left(\int_0^1 f'((1-t)u+tv)\,dt\right)(v-u)=f(v)-f(u)$
-- statement:
--   Let $s\subseteq\mathbb{C}$ be convex, let $f:\mathbb{C}\to\mathbb{C}$ be complex analytic at every point of $s$, and let $u,v\in s$. Then
--   $$
--   \left(\int_0^1 f'\big((1-t)u+tv\big)\,dt\right)(v-u)=f(v)-f(u).
--   $$
--
--   Consequently, for $u\neq v$ the integral of $f'$ along the segment from $u$ to $v$ equals the divided difference $\frac{f(v)-f(u)}{v-u}$. This integral representation of divided differences is what allows them to be treated as analytic functions of both endpoints, as in the expression $c-uv\,\frac{g(u)-g(v)}{u-v}$ attached to the exterior map $\zeta\mapsto c\zeta+g(1/\zeta)$.
--
--   **Formalization Note** The integral is `chordIntegral (deriv f) (fun _ => 1) u v`, an integral over the subtype `Set.Icc (0:ℝ) 1` with the restriction of Lebesgue measure, and $f'$ is `deriv f`. Openness of $s$ is not needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/CompactIntegrals.lean#L162-L177

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_87 u_88 u_89 u_90 u_91 u_92 u_93
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate

theorem OAI.DirectCrouzeix.Faber.chordIntegral_deriv_mul {s : Set ℂ} (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    chordIntegral (deriv f) (fun _ => 1) u v * (v-u) = f v - f u := by sorry
