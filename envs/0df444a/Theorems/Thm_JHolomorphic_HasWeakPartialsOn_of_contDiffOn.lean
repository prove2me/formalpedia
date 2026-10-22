-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
-- name    : JHolomorphic.HasWeakPartialsOn.of_contDiffOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T21:11:38.170227+00:00
-- url     : https://prove2.me/theorems/a0f93260-cf2b-4043-b001-d15a06a24881
-- title:
--   Classical partial derivatives of a $C^1$ map on an open set are weak partial derivatives
-- statement:
--   Let $E$ be a real normed space, let $U\subseteq\mathbb{C}$ be open, and let $u:\mathbb{C}\to E$ be $C^1$ on $U$. Then the classical partial derivatives $Du(z)\,1$ and $Du(z)\,i$ are weak partial derivatives of $u$ on $U$ in the sense of `HasWeakPartialsOn`: for every real $C^\infty$ function $\varphi$ with compact support in $U$,
--   $$\int_{\mathbb{C}}\bigl(D\varphi(z)\,1\bigr)\,u(z)\,dz=-\int_{\mathbb{C}}\varphi(z)\,Du(z)\,1\,dz,\qquad \int_{\mathbb{C}}\bigl(D\varphi(z)\,i\bigr)\,u(z)\,dz=-\int_{\mathbb{C}}\varphi(z)\,Du(z)\,i\,dz.$$
--   This is the basic compatibility between classical and weak derivatives, used to compare weak partials with classical ones.
--
--   **Formalization Note** $C^1$ on $U$ is `ContDiffOn ℝ 1 u U`; $Du(z)$ is `fderiv ℝ u z`, and $Du(z)$ is only used at points of $U$ after multiplication by $\varphi$.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, §5.2.1

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory
open scoped ContDiff

/-- If `u : ℂ → E` is `C¹` on an open set `U`, then its classical partial derivatives
`Du(z) 1` and `Du(z) i` are weak partial derivatives of `u` on `U`. -/
theorem HasWeakPartialsOn.of_contDiffOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} (hU : IsOpen U) {u : ℂ → E} (hu : ContDiffOn ℝ 1 u U) :
    HasWeakPartialsOn U u (fun z => fderiv ℝ u z 1) (fun z => fderiv ℝ u z Complex.I) := by
  sorry

end JHolomorphic
