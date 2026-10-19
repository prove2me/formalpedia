-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_poisson_tail_bound
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.poisson_tail_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:51:36.950725+00:00
-- url     : https://prove2.me/theorems/60887c42-46e5-4b95-b309-ae09b3f3a431
-- title:
--   Uniform $N^{-2}(1+|l|)^{-2}$ decay of nonstationary quadratic-phase integrals
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be smooth ($C^\infty$) with compact support, and let $A\ge0$ be such that the closed support of $g$ lies in $[-A,A]$. For real $t,u$ write $\varphi_{t,u}(x)=\exp\bigl(2\pi i\,(tx^2/2-ux)\bigr)$ for the quadratic phase with curvature $t$ and linear frequency $u$. Let $B\ge0$ and $\beta,L\in\mathbb{R}$ with $L\ge2(|\beta|A+B)+1$.
--
--   Then there is a constant $C\ge0$, independent of $N$, $b$ and $l$, such that for every real $N>0$, every $b\in\mathbb{R}$ with $|b|\le B$ and every integer $l$ with $|l|\ge L$,
--   $$
--   N^2\,\Bigl|\int_{\mathbb{R}}g(x)\,\varphi_{N\beta,\,N(l-b)}(x)\,dx\Bigr|\le\frac{C}{(1+|l|)^2}.
--   $$
--
--   The integrals $\int g(x)\,e^{2\pi iN(\beta x^2/2-(l-b)x)}\,dx$ are the dual terms produced by Poisson summation of a sampled chirp $k\mapsto g(k/N)\,e^{2\pi i(\beta k^2/(2N)+bk)}$, indexed by the dual frequency $l$. For $|l|\ge L$ the phase has no stationary point on the support of $g$, and the theorem bounds all these far terms at once by $CN^{-2}$ times the summable weight $(1+|l|)^{-2}$, uniformly in $N$ and in $|b|\le B$.
--
--   **Formalization Note** `phase t u x` is $\varphi_{t,u}(x)$, the support hypothesis is `tsupport g ⊆ Set.Icc (-A) A`, smoothness is `ContDiff ℝ ∞ g`, and the right-hand side is written `C * latticeWeight l` with `latticeWeight l = 1/(1+|l|)^2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingTail.lean#L76-L109

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.poisson_tail_bound {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {A B β L : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (hL : 2*(|β| * A+B)+1≤L) :
    ∃ C : ℝ, 0≤C ∧ ∀ N b : ℝ, 0<N → |b|≤B → ∀ l : ℤ,
      L≤|(l : ℝ)| →
      N^2*‖∫ x : ℝ, g x*phase (N*β) (N*((l : ℝ)-b)) x‖≤C*latticeWeight l := by sorry
