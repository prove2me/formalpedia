-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_hasDerivAt_integral_compact
-- name    : OAI.DirectCrouzeix.Faber.hasDerivAt_integral_compact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:35:01.373576+00:00
-- url     : https://prove2.me/theorems/c9243a96-1656-4193-aa5c-a8b1398e7502
-- title:
--   Complex differentiation under the integral sign over a compact parameter space
-- statement:
--   Let $\alpha$ be a compact, second-countable topological space equipped with a $\sigma$-algebra that contains all open sets, and let $\mu$ be a finite measure on $\alpha$. Let $E$ be a complex Banach space, let $s\subseteq\mathbb{C}$ be open, and let $f,f':\mathbb{C}\times\alpha\to E$ be functions such that
--   1. $(w,t)\mapsto f(w,t)$ and $(w,t)\mapsto f'(w,t)$ are continuous on $s\times\alpha$;
--   2. for every $z\in s$ and every $t\in\alpha$, the map $w\mapsto f(w,t)$ is complex differentiable at $z$ with derivative $f'(z,t)$.
--
--   Then for every $z\in s$ the function $w\mapsto\int_\alpha f(w,t)\,d\mu(t)$ is complex differentiable at $z$, and
--   $$
--   \frac{d}{dw}\Big|_{w=z}\int_\alpha f(w,t)\,d\mu(t)=\int_\alpha f'(z,t)\,d\mu(t).
--   $$
--
--   This is a form of differentiation under the integral sign in which joint continuity on $s\times\alpha$ replaces an explicit domination hypothesis. It is used to differentiate integrals along segments $t\mapsto(1-t)u+tv$, $t\in[0,1]$, with respect to their endpoints, which shows that divided differences of analytic functions are analytic in each variable.
--
--   **Formalization Note** The integrals are Bochner integrals, $f$ and $f'$ are curried functions `ℂ → α → E`, and joint continuity is `ContinuousOn f.uncurry (s ×ˢ univ)`. The measurability assumption on $\alpha$ is `OpensMeasurableSpace α`, and finiteness of $\mu$ is `IsFiniteMeasure μ`. Values of $f$ and $f'$ outside $s$ are unconstrained; this is harmless because the derivative at $z$ only depends on values near $z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/CompactIntegrals.lean#L46-L71

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

theorem OAI.DirectCrouzeix.Faber.hasDerivAt_integral_compact {α : Type u_92} {E : Type u_93}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [CompactSpace α] [SecondCountableTopology α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ] {s : Set ℂ} (hs : IsOpen s)
    {f f' : ℂ → α → E}
    (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hf' : ContinuousOn f'.uncurry (s ×ˢ univ))
    (hd : ∀ z ∈ s, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z)
    {z : ℂ} (hz : z ∈ s) :
    HasDerivAt (fun w => ∫ t, f w t ∂μ) (∫ t, f' z t ∂μ) z := by sorry
