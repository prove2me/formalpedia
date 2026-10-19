-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_uniform_poisson_chirp
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.uniform_poisson_chirp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:53:17.617192+00:00
-- url     : https://prove2.me/theorems/d76990be-8e47-4797-99e1-a8b8e08dfc01
-- title:
--   Uniform stationary-phase asymptotics for Poisson-summed sampled chirps
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be smooth with compact support, let $A,B\ge0$ be such that the closed support of $g$ lies in $[-A,A]$, and let $\beta\neq0$ be real. For real $N$ and $b$ and an integer $l$ define the *stationary wave*
--   $$
--   W_{N,b}(l)=\frac{1}{\sqrt{|\beta|}}\exp\Bigl(2\pi i\Bigl(\frac{\operatorname{sgn}\beta}{8}-\frac{N(l-b)^2}{2\beta}\Bigr)\Bigr)\,g\Bigl(\frac{l-b}{\beta}\Bigr),
--   $$
--   the contribution predicted by stationary phase from the dual frequency $l$, whose stationary point is $x=(l-b)/\beta$.
--
--   There exist a finite set $J\subset\mathbb{Z}$ and a constant $C\ge0$ such that for every real $N\ge1$ and every real $b$ with $|b|\le B$:
--
--   1. $W_{N,b}(l)=0$ for every integer $l\notin J$;
--   2. the normalized sampled chirp sum is approximated by the finitely many stationary waves:
--   $$
--   \Bigl|\frac{1}{\sqrt N}\sum_{k\in\mathbb{Z}}g\Bigl(\frac kN\Bigr)\exp\Bigl(2\pi i\Bigl(\frac{\beta k^2}{2N}+bk\Bigr)\Bigr)-\sum_{l\in J}W_{N,b}(l)\Bigr|\le\frac{C}{N}.
--   $$
--
--   The sum over $k$ has only finitely many nonzero terms because $g$ has compact support, and $J$ and $C$ do not depend on $N$ or $b$. Thus the sampled chirp sum $\sum_k g(k/N)\,e^{2\pi i(\beta k^2/(2N)+bk)}$ equals $\sqrt N$ times an explicit finite combination of unimodular phases with weights $g((l-b)/\beta)/\sqrt{|\beta|}$, up to an error $O(N^{-1/2})$ that is uniform in the linear frequency $|b|\le B$. This one-mode estimate underlies both the sup-norm and the mean-square analysis of sums of sampled chirps.
--
--   **Formalization Note** `stationaryWave g N β b l` is $W_{N,b}(l)$ (with `Real.sign`, which is $\pm1$ here), the exponential in the sum is `phase (β/N) (-b) k`, where `phase t u x` $=\exp(2\pi i(tx^2/2-ux))$, the sum over $k$ is a `tsum` over $\mathbb{Z}$, and $1/\sqrt N$ is the complex number `1/(Real.sqrt N : ℂ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingTail.lean#L177-L245

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

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.uniform_poisson_chirp {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A B β : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (hβ : β≠0) :
    ∃ J : Finset ℤ, ∃ C : ℝ, 0≤C ∧ ∀ N b : ℝ, 1≤N → |b|≤B →
      (∀ l∉J, stationaryWave g N β b l=0) ∧
      ‖(1/(Real.sqrt N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)*phase (β/N) (-b) k)-
        ∑ l∈J, stationaryWave g N β b l‖≤C/N := by sorry
