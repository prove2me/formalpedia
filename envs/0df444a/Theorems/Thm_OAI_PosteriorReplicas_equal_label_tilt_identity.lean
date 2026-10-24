-- Prove2me | Theorems.Thm_OAI_PosteriorReplicas_equal_label_tilt_identity
-- name    : OAI.PosteriorReplicas.equal_label_tilt_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:33:50.626518+00:00
-- url     : https://prove2.me/theorems/2202f44b-ca23-42f9-a1a5-9fa6d544e26c
-- title:
--   The equal-label identity for a bounded tilt, Left(H) = Right(H) (OpenAI posterior replicas, identity (25))
-- statement:
--   **Notation** (from the published bundle `Def_PosteriorReplicas`). The base law $P_0$ (`BaseLaw.measure`) is the uniform probability on the unit sphere of $\mathbb R^d$ or the standard Gaussian, and $\nu = f P_0$. For a $k \times d$ matrix $A$ and labels $y \in \mathbb R^k$, $p_A(y)$ (`projectedDensity`) is the density at $y$ of $Ax$ under $P_0$ (`baseDensity`) times the integral of $f$ over the conditional law of $P_0$ on $\{Ax = y\}$ (`baseFiber`), and $\nu_{A,y}$ (`tiltedFiber`) is that conditional law reweighted by $f$ and normalized (a Dirac mass when the weight is $0$). For a tuple $u = (u_0, \dots, u_m)$, $J(u)$ (`affineVolume`) is the square root of the Gram determinant of the differences $u_i - u_0$, and $F_u$ (`constrainedRows k u`) is the law of a standard Gaussian $k \times d$ matrix with its rows projected orthogonally onto the complement of the span of those differences. With $\gamma_{k,d}$ the standard Gaussian law of $A$ (`gaussianRows d k`), and $H \ge 0$ on triples $(A, y, u)$ (the type `EqualSpace d k m`):
--   $$\mathrm{Left}(H) = \int \gamma_{k,d}(dA) \int_{\mathbb R^k} p_A(y)^{m+1} \int H(A, y, u)\, \nu_{A,y}^{\otimes(m+1)}(du)\, dy \quad (\texttt{equalLabelLeft}),$$
--   $$\mathrm{Right}(H) = (2\pi)^{-km/2} \int J(u)^{-k} \int H(A, Au_0, u)\, F_u(dA)\, \nu^{\otimes(m+1)}(du) \quad (\texttt{equalLabelRight}).$$
--
--   **The statement.** Let $k, m \ge 1$ with $k + m + 2 \le d$, let $P_0$ be either base law, and let $f \ge 0$ be measurable with $f \le L$ for a finite $L$. Then $\mathrm{Left}(H) = \mathrm{Right}(H)$ for every measurable $H \ge 0$.
--
--   Lean: `OAI.PosteriorReplicas.equal_label_tilt_identity`, OpenAI's lemma of that name (in `lean/OAI/Probability/PosteriorReplicas/Measures/EqualLabelIdentity.lean`). `EqualSpace` comes from the definitions bundle `OAIQWPR000` of this split.
-- source:
--   OpenAI, Posterior replicas and conditional information in Gaussian regression, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf, Theorem 3.3, identity (25); Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/PosteriorReplicas/Measures/EqualLabelIdentity.lean (declaration OAI.PosteriorReplicas.equal_label_tilt_identity)

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
noncomputable section
namespace PosteriorReplicas

lemma equal_label_tilt_identity {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    equalLabelLeft base f H = equalLabelRight base f H := by
  sorry

end PosteriorReplicas
end

end OAI
end
