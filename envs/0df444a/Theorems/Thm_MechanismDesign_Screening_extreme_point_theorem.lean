-- Prove2me | Theorems.Thm_MechanismDesign_Screening_extreme_point_theorem
-- name    : MechanismDesign.Screening.extreme_point_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:44:42.434664+00:00
-- url     : https://prove2.me/theorems/986b4167-835c-4ecb-848c-debd560fba7d
-- title:
--   Proposition 2.4 -- Extreme Point Theorem (a linear function attains its maximum at an extreme point)
-- statement:
--   Let $X$ be a nonempty, compact, convex subset of a real normed vector space $E$, and let $f$ be a linear function on $E$ whose restriction to $X$ is continuous. Then the set $\mathcal E$ of extreme points of $X$ (Definition 2.4) is nonempty, and there is an $e\in\mathcal E$ with
--   $$f(e)\ge f(x)\qquad\text{for all } x\in X .$$
--
--   Applied to the seller's revenue on $M$, this shows it suffices to consider extreme points of $M$, i.e. deterministic allocation rules (Lemma 2.7). The book cites this as the "Extreme Point Theorem" of Ok (2007, p.658).
--
--   **Formalization Note** Two readings are made explicit. (1) $X$ is assumed nonempty: the book omits this, and for $X=\emptyset$ the set of extreme points is empty, so the statement as printed is false there. (2) "$f:X\to\mathbb R$ continuous linear" is read as a linear map $f:E\to\mathbb R$ that is continuous on $X$ (a function defined only on a convex set cannot itself be linear); continuity is not required on all of $E$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.16, Proposition 2.4 (citing Ok, Real Analysis with Economic Applications, 2007, p.658)

import Mathlib
import Definitions.Def_MechanismDesign_Screening_ExtremePoints

namespace MechanismDesign.Screening

/-- **Proposition 2.4 (Extreme Point Theorem)**, p.16 (Ok 2007, p.658). Let `X` be a nonempty,
compact, convex subset of a real normed vector space `E`, and let `f` be a linear function that is
continuous on `X`. Then the set of extreme points of `X` (Definition 2.4) is nonempty, and some
extreme point `e` satisfies `f(e) ≥ f(x)` for all `x ∈ X`. -/
theorem extreme_point_theorem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hne : X.Nonempty) (hcomp : IsCompact X) (hconv : Convex ℝ X)
    (f : E →ₗ[ℝ] ℝ) (hf : ContinuousOn f X) :
    {e | IsExtremePoint X e}.Nonempty ∧ ∃ e, IsExtremePoint X e ∧ ∀ x ∈ X, f x ≤ f e := by sorry

end MechanismDesign.Screening
