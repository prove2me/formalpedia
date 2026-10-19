-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_translate
-- name    : HunterPDE.Sobolev.HasWeakDeriv.translate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T11:03:50.189095+00:00
-- url     : https://prove2.me/theorems/c6ca6526-a3eb-41cd-a524-df21e60099ba
-- title:
--   Translation covariance of whole-space weak derivatives
-- statement:
--   Let $\alpha$ be any multi-index in $\mathbb R^n$ and suppose that $g$ is the weak derivative $D^\alpha f$ on the whole space, in the sense of the distributional test-function identity, with both functions locally integrable. For every vector $a$, the translated functions satisfy
--   $$D^\alpha(f(\cdot-a))=g(\cdot-a)$$
--   in the same weak sense. No Sobolev membership or global integrability hypothesis is needed.
-- source:
--   Translation covariance derived from J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Definition 3.2 (printed p.48); used in the translation and mollification argument following Theorem 3.44 (p.73). Translate the test function by the opposite vector and apply translation invariance of Lebesgue measure.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory HunterPDE.Sobolev
set_option autoImplicit false

theorem HunterPDE.Sobolev.HasWeakDeriv.translate {n : ℕ} {α : Fin n → ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasWeakDeriv Set.univ α f g) (a : EuclideanSpace ℝ (Fin n)) :
    HasWeakDeriv Set.univ α (fun x => f (x-a)) (fun x => g (x-a)) := by sorry
