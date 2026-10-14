-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_hasWeakDeriv_of_contDiff
-- name    : HunterPDE.Sobolev.hasWeakDeriv_of_contDiff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T22:59:00.172599+00:00
-- url     : https://prove2.me/theorems/519db1ba-3f7a-42a2-a160-341568ebf682
-- title:
--   Classical derivatives of smooth functions are weak derivatives
-- statement:
--   Let $u:\mathbb R^n\to\mathbb R$ be smooth and let $\alpha\in\mathbb N_0^n$ be a multi-index. Its classical derivative is also its weak derivative on the whole space:
--
--   $$\int_{\mathbb R^n}D^\alpha u\,\psi\,dx
--   =(-1)^{|\alpha|}\int_{\mathbb R^n}u\,D^\alpha\psi\,dx
--   \qquad(\psi\in C_c^\infty(\mathbb R^n)).$$
--
--   Both $u$ and its classical derivative are locally integrable. No compact support or global integrability assumption on $u$ is imposed. This identifies classical and weak derivatives of smooth functions for Sobolev and distribution arguments, including order zero and dimension zero.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Section 1.8 (p. 10), Definitions 3.1–3.2 (pp. 47–48). Supporting calculus result: repeated integration by parts and support locality of derivatives.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.hasWeakDeriv_of_contDiff {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (α : Fin n → ℕ) :
    HasWeakDeriv Set.univ α u (iteratedPartial α u) := by sorry
