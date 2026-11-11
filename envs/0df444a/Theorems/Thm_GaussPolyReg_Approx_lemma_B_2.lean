-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_lemma_B_2
-- name    : GaussPolyReg.Approx.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:38.307888+00:00
-- url     : https://prove2.me/theorems/dd1744df-ab78-498a-85a4-02df9a8b46e5
-- title:
--   Lemma B.2 — Hermite product moments count labeled matchings
-- statement:
--   Let $I$ be any index set of independent standard Gaussians, and let $\alpha_1,\ldots,\alpha_\ell:I\to\mathbb N$ be finitely supported. Group $j$ contains $\alpha_{j,i}$ distinct objects of label $i$. Let $\mathcal M$ be the perfect matchings with no pair inside one group. Then
--
--   $$\mathbb E\prod_{j=1}^\ell\mathrm{He}_{\alpha_j}(X)=\sum_{M\in\mathcal M}\prod_{uv\in M}\mathbf1_{\mathrm{label}(u)=\mathrm{label}(v)}.$$
--
--   The right-hand side counts exactly the label-compatible matchings. This is the combinatorial moment identity used by the tensor diagram expansions.
--
--   Differences from the source:
--   - encoding: sum of products of label-equality indicators over perfect matchings → cardinality of the explicit finite set of label-compatible involutions on the grouped objects; reason: each matching contributes one exactly when every paired label agrees; each involution represents one unoriented matching
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma B.2, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Tensors

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem lemma_B_2 {I : Type*} (ℓ : ℕ) (α : Fin ℓ → I →₀ ℕ) :
    (∫ x, ∏ j, heMulti (α j) x ∂gaussianProduct I) =
      ((labelMatchings α).card : ℝ) := by sorry

end GaussPolyReg.Approx
