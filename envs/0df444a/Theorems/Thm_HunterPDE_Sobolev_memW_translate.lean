-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_memW_translate
-- name    : HunterPDE.Sobolev.memW_translate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T09:39:30.222364+00:00
-- url     : https://prove2.me/theorems/8fe14d1f-66f2-451b-acb2-39eafbcbbdb6
-- title:
--   Translation invariance of whole-space Sobolev membership
-- statement:
--   Let $k\ge0$, let $p\in[0,\infty]$, and let $f\in W^{k,p}(\mathbb R^n)$. For every vector $a\in\mathbb R^n$, the translate
--   $$\tau_a f(x)=f(x-a)$$
--   belongs to $W^{k,p}(\mathbb R^n)$. The Sobolev predicate includes local integrability. No restriction on $p$ is needed: translating the distributional identities transports each weak derivative, and translation preserves Lebesgue measure.
-- source:
--   Translation covariance of distributional derivatives and invariance of Lebesgue measure. J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Definition 3.2 (printed p.48), Definition 3.23 (p.58), and the translation/mollification outline after Theorem 3.44 (p.73). This is the whole-space, arbitrary-order translation ingredient, stated separately from continuity.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory HunterPDE.Sobolev
set_option autoImplicit false

theorem HunterPDE.Sobolev.memW_translate {n k : ℕ} {p : ENNReal}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (a : EuclideanSpace ℝ (Fin n)) :
    MemW k p Set.univ (fun x => f (x - a)) := by sorry
