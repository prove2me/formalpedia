-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_affine_normalization_408915f
-- name    : FunctionalInequalities.Analysis.exists_affine_normalization_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:44.621419+00:00
-- url     : https://prove2.me/theorems/51e8ec67-682a-45d1-843f-50ad7ea850c3
-- title:
--   Affine Normalization of Compact Convex Sets
-- statement:
--   This formalizes the affine normalization statement used in the weak Letwin route.
--
--   Let $E$ be a finite-dimensional real inner-product space. There exists a constant $C>0$, depending only on $E$, such that for every compact convex set $K\subseteq E$ with nonempty interior, there is an affine equivalence $e:E\simeq_A E$ satisfying
--
--   $$
--   \overline B(0,1)\subseteq e(K)\subseteq\overline B(0,C).
--   $$
--
--   The declaration is `exists_affine_normalization`. The result is existential in both $C$ and the affine equivalence and does not provide a uniform constant across different ambient spaces.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L515-L736 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, declaration `FunctionalInequalities.Analysis.exists_affine_normalization`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Mathlib

noncomputable section
open Set Matrix
section LT11D4AffineNormalizationAssembly
open Set Metric
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 4000000

theorem FunctionalInequalities.Analysis.exists_affine_normalization_408915f {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ e : E ≃ᵃ[ℝ] E, closedBall (0 : E) 1 ⊆ e '' K ∧ e '' K ⊆ closedBall (0 : E) C := by sorry
