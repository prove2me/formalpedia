-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_curved_average_zero
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.curved_average_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:54:12.445919+00:00
-- url     : https://prove2.me/theorems/f7ee8a90-ae39-461d-9e6f-b6c92015cd94
-- title:
--   Normalized sampled chirp averages with nonzero curvature tend to zero
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be smooth with compact support, with closed support contained in $[-A,A]$ for some $A\ge0$, and with $|g(x)|\le D$ for all $x\in\mathbb{R}$, where $D\ge0$. Let $\beta\neq0$ and $b$ be real numbers. Then, as $N\to\infty$ through the positive integers,
--   $$
--   \Bigl|\frac1N\sum_{k\in\mathbb{Z}}g\Bigl(\frac kN\Bigr)\exp\Bigl(2\pi i\Bigl(\frac{\beta k^2}{2N}+bk\Bigr)\Bigr)\Bigr|\longrightarrow0 .
--   $$
--   (The sum has finitely many nonzero terms since $g$ has compact support.)
--
--   Without the quadratic term this would be a Riemann sum for $\int g$ twisted by $e^{2\pi ibk}$; the theorem says that a nonzero curvature $\beta$ alone already destroys all mass in the limit. When the mean square of a sum of sampled chirp modes is expanded, each cross term between two modes of different curvatures $\lambda_p\neq\lambda_q$ is an average of this form, with $\beta=\lambda_p-\lambda_q$ and $g$ the product of one amplitude with the conjugate of the other, so such cross terms disappear in the limit.
--
--   **Formalization Note** The exponential is `phase (β/N) (-b) k`, where `phase t u x` $=\exp(2\pi i(tx^2/2-ux))$; the sum over $k$ is a `tsum` over $\mathbb{Z}$; $N$ ranges over $\mathbb{N}$ (at $N=0$ Lean reads $1/N$ as $0$, which does not affect the limit), and the limit is stated with `Tendsto` along `atTop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingEnergy.lean#L10-L52

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
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.curved_average_zero {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A D β : ℝ} (hA : 0≤A) (hD : 0≤D)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (hbound : ∀ x, ‖g x‖≤D)
    (hβ : β≠0) (b : ℝ) :
    Tendsto (fun N : ℕ ↦ ‖(1/(N : ℂ))*(∑' k : ℤ,
      g ((k : ℝ)/N)*phase (β/N) (-b) k)‖) atTop (𝓝 0) := by sorry
