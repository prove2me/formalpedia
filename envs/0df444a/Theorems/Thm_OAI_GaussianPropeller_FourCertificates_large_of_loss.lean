-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_of_loss
-- name    : OAI.GaussianPropeller.FourCertificates.large_of_loss
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:18:47.438986+00:00
-- url     : https://prove2.me/theorems/30d0fae4-397a-409d-8982-4a95c37ffbfd
-- title:
--   Certificate for large cells: if loss(x) ≥ (9/8π)r²/(1+√(1−4r²/3)) with 2/5 ≤ r ≤ 21/40, then the Gaussian tail p(x) exceeds 13r²/20 + 9/100 (OpenAI Gaussian propeller)
-- statement:
--   For real $x$ let $p(x) = (2\pi)^{-1/2}\int_x^\infty e^{-t^2/2}\,dt$, the standard normal upper tail (`ProbabilityBounds.p`, with `OneCell.gaussianConst` $= (2\pi)^{-1/2}$ and `OneCell.tail`). Let $\lambda(x) = e^{-x^2/2}/\int_x^\infty e^{-t^2/2}\,dt$ (`Mills.lambda`), $G(x) = \lambda(x)(\lambda(x) - x)$ (`Mills.G`) and $\mathrm{loss}(x) = p(x)^2\,G(x)$ (`ProbabilityBounds.loss`). The integrals are over the open half-line $(x, \infty)$.
--
--   Let $r$ and $x$ be real numbers with $2/5 \le r \le 21/40$ and $x \ge 0$, and suppose
--   $$\frac{9}{8\pi}\cdot\frac{r^2}{1 + \sqrt{1 - \tfrac43 r^2}} \;\le\; \mathrm{loss}(x).$$
--   Then
--   $$\tfrac{13}{20}\,r^2 + \tfrac{9}{100} \;<\; p(x)$$
--   (the left side is `FourCertificates.large r`).
--
--   Lean: `OAI.GaussianPropeller.FourCertificates.large_of_loss`, OpenAI's lemma of that name (in `lean/OAI/Probability/GaussianPropeller/LossCertificates.lean`). `p`, `loss`, `gaussianConst`, `tail`, `density`, `lambda`, `G` and `large` come from the definitions bundle `OAIQWGP000` of this split.
-- source:
--   OpenAI, The Gaussian propeller bound in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 096; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianPropeller/LossCertificates.lean (declaration OAI.GaussianPropeller.FourCertificates.large_of_loss)

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Definitions.Def_OAIQWGP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor

lemma large_of_loss {r x:ℝ} (hr:r∈Icc (2/5:ℝ) (21/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  sorry

end GaussianPropeller.FourCertificates

end OAI
end
