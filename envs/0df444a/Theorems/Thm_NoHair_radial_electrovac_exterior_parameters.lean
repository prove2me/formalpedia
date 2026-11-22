-- Prove2me | Theorems.Thm_NoHair_radial_electrovac_exterior_parameters
-- name    : NoHair.radial_electrovac_exterior_parameters
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:55:55.362448+00:00
-- url     : https://prove2.me/theorems/3db1ae22-a131-41c1-a2ba-44b51996966c
-- title:
--   Integration of the spherical Einstein–Maxwell equations up to the outer horizon
-- statement:
--   Let $R>0$ be an areal horizon radius. Let $\mu(r)$ be the mass inside radius $r$, and let $u(r),v(r)$ be radial electric and magnetic field amplitudes. Suppose $\mu$ is continuous on $[R,\infty)$, $2\mu(R)=R$, and $2\mu(r)<r$ for $r>R$. Suppose the spherical source-free Einstein–Maxwell equations hold on the open exterior,
--   $$
--   u'=-2u/r,\qquad v'=-2v/r,\qquad 2\mu'=r^2(u^2+v^2).
--   $$
--
--   There exist a mass $m>0$, a charge magnitude $e\ge0$ with $e^2\le m^2$, and a constant duality angle $\beta$ such that
--   $$
--   R=m+\sqrt{m^2-e^2},\qquad
--   \mu(r)=m-\frac{e^2}{2r},\qquad
--   r^2u(r)=e\cos\beta,\quad r^2v(r)=e\sin\beta
--   \qquad(r>R).
--   $$
--
--   The characterization includes a double horizon root and simultaneous vanishing of both fluxes.
-- source:
--   K. A. Bronnikov, Dyonic configurations in nonlinear electrodynamics coupled to general relativity, arXiv:1708.08125, p. 1, Eqs. (2)–(5) and p. 4, Eq. (10), Maxwell specialization, https://arxiv.org/pdf/1708.08125. The horizon is a zero of the metric coefficient in Eq. (10).

import Definitions.Def_NoHair_coordinates

open Set NoHair

theorem NoHair.radial_electrovac_exterior_parameters (R : ℝ) (μ u v : ℝ → ℝ)
    (hR : 0 < R) (hcont : ContinuousOn μ (Ici R)) (horizon : 2 * μ R = R)
    (exterior : ∀ r, R < r → 2 * μ r < r)
    (electric : ∀ r, R < r → HasDerivAt u (-2 * u r / r) r)
    (magnetic : ∀ r, R < r → HasDerivAt v (-2 * v r / r) r)
    (mass : ∀ r, R < r → HasDerivAt μ (r ^ 2 * (u r ^ 2 + v r ^ 2) / 2) r) :
    ∃ m e β : ℝ, 0 ≤ e ∧ IsKerrNewmanBlackHoleParams m 0 e ∧
      kerrNewmanOuterRadius m 0 e = R ∧
      ∀ r, R < r → μ r = m - e ^ 2 / (2 * r) ∧
        r ^ 2 * u r = Real.cos β * e ∧ r ^ 2 * v r = Real.sin β * e := by sorry
