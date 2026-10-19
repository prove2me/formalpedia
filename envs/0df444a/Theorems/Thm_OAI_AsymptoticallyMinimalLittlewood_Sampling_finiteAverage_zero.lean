-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_finiteAverage_zero
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.finiteAverage_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:58:40.249436+00:00
-- url     : https://prove2.me/theorems/b58e14c5-a8fb-430d-802b-bc9693f4754c
-- title:
--   Vanishing of nonresonant finite chirp averages
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be smooth with compact support, with closed support contained in the open interval $(0,1)$, and with $|g(x)|\le D$ for all $x$, where $D\ge0$. Let $\beta,b\in\mathbb{R}$ satisfy the nonresonance condition
--   $$
--   \beta\neq0\quad\text{or}\quad b\notin\mathbb{Z}.
--   $$
--   For a positive integer $N$ define the finite chirp average
--   $$
--   \mathcal A_N(g;\beta,b)=\frac1N\sum_{k=0}^{N-1}g\Bigl(\frac kN\Bigr)\exp\Bigl(2\pi i\Bigl(\frac{\beta k^2}{2N}+bk\Bigr)\Bigr).
--   $$
--   Then $|\mathcal A_N(g;\beta,b)|\to0$ as $N\to\infty$.
--
--   The averages $\mathcal A_N$ are exactly the off-diagonal terms that appear when the mean square of a finite sum of sampled chirp modes $k\mapsto c\,g(k/N)\exp(2\pi i(\lambda k^2/(2N)+bk))$ is expanded: $g$ is then the product of one amplitude with the conjugate of another, $\beta$ is the difference of the curvatures and $b$ the difference of the linear frequencies. The theorem says that such a cross term vanishes asymptotically unless the two modes have equal curvature and linear frequencies differing by an integer.
--
--   **Formalization Note** `finiteAverage g N β b` is $\mathcal A_N(g;\beta,b)$, with the exponential written `phase (β/N) (-b) k`, where `phase t u x` $=\exp(2\pi i(tx^2/2-ux))$; at $N=0$ Lean's convention $1/0=0$ makes it $0$, which does not affect the limit. The condition $b\notin\mathbb{Z}$ is stated as `∀ l : ℤ, (l : ℝ) ≠ b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingEnergy.lean#L219-L235

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

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.finiteAverage_zero {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hsupp : tsupport g⊆Set.Ioo (0:ℝ) 1)
    {D β b : ℝ} (hD : 0≤D) (hbound : ∀ x, ‖g x‖≤D)
    (hfreq : β≠0 ∨ ∀ l : ℤ, (l : ℝ)≠b) :
    Tendsto (fun N : ℕ ↦ ‖finiteAverage g N β b‖) atTop (𝓝 0) := by sorry
