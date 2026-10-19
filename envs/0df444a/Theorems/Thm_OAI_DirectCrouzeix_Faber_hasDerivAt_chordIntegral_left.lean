-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_hasDerivAt_chordIntegral_left
-- name    : OAI.DirectCrouzeix.Faber.hasDerivAt_chordIntegral_left
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:35:33.31771+00:00
-- url     : https://prove2.me/theorems/363b2570-8c2f-4732-9ac8-1860dd494b06
-- title:
--   Derivative of a weighted chord integral with respect to its left endpoint
-- statement:
--   For $f:\mathbb{C}\to\mathbb{C}$, a weight $w:[0,1]\to\mathbb{C}$ and $u,v\in\mathbb{C}$, define the chord integral of $f$ along the segment from $u$ to $v$:
--   $$
--   I_w[f](u,v)=\int_0^1 w(t)\,f\big((1-t)u+tv\big)\,dt .
--   $$
--   Let $s\subseteq\mathbb{C}$ be open and convex, let $f$ be complex analytic at every point of $s$, let $w$ be continuous on $[0,1]$, and let $u,v\in s$. Then the function $z\mapsto I_w[f](z,v)$ is complex differentiable at $u$, and its derivative there is the chord integral of $f'$ with weight $(1-t)\,w(t)$:
--   $$
--   \frac{\partial}{\partial u}\,I_w[f](u,v)=\int_0^1 w(t)\,(1-t)\,f'\big((1-t)u+tv\big)\,dt .
--   $$
--
--   Chord integrals represent divided differences: for $g$ analytic on a convex set containing $u\neq v$ one has $\int_0^1g'((1-t)u+tv)\,dt=\frac{g(u)-g(v)}{u-v}$. The formula above shows that such divided differences are complex differentiable in the left variable with derivative again a chord integral. This is how the correction kernels in the Faber expansion are shown to be analytic.
--
--   **Formalization Note** The parameter interval is the subtype `Set.Icc (0:ℝ) 1` with the restriction of Lebesgue measure, $I_w[f](u,v)$ is `chordIntegral f w u v`, $f'$ is `deriv f`, and analyticity on $s$ is `AnalyticOnNhd ℂ f s`. The new weight is `fun t => w t * ((1 - t : ℝ) : ℂ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/CompactIntegrals.lean#L107-L125

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

theorem OAI.DirectCrouzeix.Faber.hasDerivAt_chordIntegral_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    HasDerivAt (fun z => chordIntegral f w z v)
      (chordIntegral (deriv f) (fun t => w t * ((1-(t : ℝ) : ℝ) : ℂ)) u v) u := by sorry
