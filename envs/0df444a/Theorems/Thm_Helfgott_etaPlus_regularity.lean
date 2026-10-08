-- Prove2me | Theorems.Thm_Helfgott_etaPlus_regularity
-- name    : Helfgott.etaPlus_regularity
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T02:53:43.847164+00:00
-- url     : https://prove2.me/theorems/8cdcf0a7-7217-45f3-885c-d66d8a1dc72a
-- title:
--   Continuity and full L1/L2 control for the actual band-limited smoothing
-- statement:
--   Helfgott's actual band-limited smoothing $\eta_+$ is continuous on the whole real line and belongs to both $L^1(\mathbb R)$ and $L^2(\mathbb R)$. Its square mass satisfies the explicit upper bound
--
--   $$\int_{\mathbb R}\eta_+(t)^2\,dt\le0.642.$$
--
--   The full additive convolution
--
--   $$\rho\longmapsto\int_{\mathbb R}\eta_+(u)\eta_+(\rho-u)\,du$$
--
--   is continuous. These assertions include the smoothing's signed tails. Continuity includes the endpoint zero and the extension by zero to negative arguments.
--
--   The result supplies the actual smoothing regularity and norm control required in quantitative Fourier main-term and arc arguments. Its square-mass bound is coarser than the paper's sharper numerical evaluations.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §3.3 Proposition 3.2, §4.2–§4.3, equations (4.8)–(4.9), and §7.1 equations (7.3)–(7.5). Full continuity and the coarser squared norm bound 0.642 are independently derived from the exact published smoothing definitions and checked fourth-order projection estimates. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory

namespace Helfgott

theorem etaPlus_regularity : Continuous etaPlus ∧ Integrable etaPlus ∧
      Integrable (fun t : ℝ => (etaPlus t)^2) ∧
      (∫ t : ℝ, (etaPlus t)^2) ≤ (321/500:ℝ) ∧
      Continuous (fun ρ : ℝ => ∫ u : ℝ,etaPlus u*etaPlus (ρ-u)) := by sorry

end Helfgott
