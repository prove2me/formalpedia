-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_sobolevNorm_translation_small
-- name    : HunterPDE.Sobolev.sobolevNorm_translation_small
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T09:40:00.894912+00:00
-- url     : https://prove2.me/theorems/1179f7bf-7b78-4172-bb9d-c4f9c73dad03
-- title:
--   Strong continuity of translations in finite-p Sobolev norms
-- statement:
--   Let $k\ge0$, $1\le p<\infty$, and $f\in W^{k,p}(\mathbb R^n)$. Translations are continuous at the identity in the Sobolev norm:
--   $$\forall\varepsilon>0\;\exists r>0\;\forall a,\quad |a|<r\Longrightarrow
--   \|f-\tau_a f\|_{W^{k,p}(\mathbb R^n)}<\varepsilon,\qquad \tau_a f(x)=f(x-a).$$
--   The tolerance may be an extended nonnegative real. The norm uses every weak derivative through order $k$. The finite-p assumption is essential for general Sobolev functions. This assertion imposes no support or boundary hypothesis.
-- source:
--   Strong Lp continuity of translations applied to the finitely many weak derivatives in Definition 3.23. J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, printed pp.58–60 (Sobolev norm and approximation) and p.73 (translation/mollification outline after Theorem 3.44). The epsilon-delta statement is the whole-space arbitrary-order analytic ingredient of that outline.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory HunterPDE.Sobolev
open scoped ENNReal
set_option autoImplicit false

theorem HunterPDE.Sobolev.sobolevNorm_translation_small {n k : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ < r →
      sobolevNorm k p Set.univ (f - (fun x => f (x - a))) < ε := by sorry
