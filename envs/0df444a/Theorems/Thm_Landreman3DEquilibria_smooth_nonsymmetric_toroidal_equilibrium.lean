-- Prove2me | Theorems.Thm_Landreman3DEquilibria_smooth_nonsymmetric_toroidal_equilibrium
-- name    : Landreman3DEquilibria.smooth_nonsymmetric_toroidal_equilibrium
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:41:38.5583+00:00
-- url     : https://prove2.me/theorems/6bb51565-a13b-4f5f-bd0f-aab8ab4fef80
-- title:
--   A smooth non-axisymmetric toroidal equilibrium with non-constant pressure
-- statement:
--   For every $0<\epsilon<1$, every $0<\delta<(1-\epsilon)^2/4$ and every constant $p_a$, the explicit pair $(B,p)$ of the integer-transform family is a smooth, non-axisymmetric solution of the ideal MHD equilibrium equations on a toroidal domain, with pressure gradient vanishing only on the magnetic axis. Concretely, all of the following hold.
--
--   1. $B$ and $p=p_a-2\psi$ are $C^\infty$ on the open set $U_\epsilon$.
--   2. $\nabla\cdot B=0$ on $U_\epsilon$.
--   3. $(\nabla\times B)\times B=\nabla p$ on $U_\epsilon$.
--   4. $B\cdot\nabla p=0$ on $U_\epsilon$, so the pressure surfaces are invariant surfaces of the field.
--   5. On the solid torus $\Omega_\delta=\{x\in U_\epsilon:\psi\le\delta\}$ the pressure gradient vanishes exactly on the magnetic axis: $\nabla p(x)=0\iff\psi(x)=0$.
--   6. The configuration is not axisymmetric: there is a rotation about the $z$ axis and a point of $\Omega_\delta$ whose image under that rotation lies in $\Omega_\delta$ and carries a different pressure.
--
--   Since MHD equilibrium is isomorphic to steady incompressible Euler flow, the same statement exhibits an explicit non-symmetric steady Euler flow with invariant tori and non-constant Bernoulli function. Grad conjectured that smooth toroidal equilibria with non-constant pressure require a continuous symmetry; this theorem is the formal statement that the family of the source paper contradicts the strict formulation of that conjecture.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eqs. (2.1)-(2.5), (2.17)-(2.18); Sections 1, 2.1, 2.3 and 4 (counterexample to the strict formulation of Grad's conjecture)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem smooth_nonsymmetric_toroidal_equilibrium (e d pa : ℝ) (he : 0 < e) (he1 : e < 1)
    (hd : 0 < d) (hd' : d < (1 - e) ^ 2 / 4) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Bfield e) (domainU e) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (pressure e pa) (domainU e) ∧
      (∀ x ∈ domainU e, divg (Bfield e) x = 0) ∧
      (∀ x ∈ domainU e, cross3 (curl (Bfield e) x) (Bfield e x) = grad (pressure e pa) x) ∧
      (∀ x ∈ domainU e, advect (Bfield e) (pressure e pa) x = 0) ∧
      (∀ x ∈ domainOmega e d, grad (pressure e pa) x = 0 ↔ psiFun e x = 0) ∧
      (∃ t : ℝ, ∃ x ∈ domainOmega e d, rotZ t x ∈ domainOmega e d ∧
        pressure e pa (rotZ t x) ≠ pressure e pa x) := by sorry

end Landreman3DEquilibria
