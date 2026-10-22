-- Prove2me | Theorems.Thm_NewtonCartan_classical_christoffel_form
-- name    : NewtonCartan.classical_christoffel_form
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:30:02.882556+00:00
-- url     : https://prove2.me/theorems/5ca17246-e257-45ed-91b7-74ab3aca0e57
-- title:
--   Christoffel form of a classical Newton–Cartan connection on $\mathbb{R}^4$
-- statement:
--   Let $(\mathbb{R}^4, t_a, h^{ab})$ be equipped with the standard absolute time $t_a = \mathrm{d}x^0$ and flat spatial metric $h^{ab} = \mathrm{diag}(0,1,1,1)$, and let $\nabla$ be a torsion-free derivative operator compatible with both metrics (a classical Newton–Cartan connection).
--
--   Then, in this global chart, the Christoffel symbols of $\nabla$ satisfy
--   $$
--   \Gamma^0{}_{bc} = 0,\qquad
--   \Gamma^i{}_{jk} = 0 \quad (i,j,k \in \{1,2,3\}),\qquad
--   \Gamma^i{}_{0j} + \Gamma^j{}_{0i} = 0.
--   $$
--   Thus the only possibly nonzero symbols are the gravitational field $\Gamma^i{}_{00}$ and the antisymmetric Coriolis field $\Omega^i{}_j = \Gamma^i{}_{0j}$.
--
--   This is the standard reduction of a classical connection on Newtonian spacetime in inertial spatial coordinates; it is the starting point for Trautman recovery.
--
--   Formalization Note. `IsClassical` packages `IsDerivOp` (smooth + torsion-free) and `Compatible` with the fixed `tt` and `hh` of `Def_NewtonCartan_defs`.
-- source:
--   D. B. Malament, Topics in the Foundations of GR and NGT (2012), §4.1–4.2; Weatherall arXiv:1411.5757

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- On $(\mathbb{R}^4, t_a, h^{ab})$ in the standard chart, a classical connection has
vanishing temporal Christoffel symbols, vanishing purely spatial Christoffel symbols, and
antisymmetric Coriolis symbols $\Omega^i{}_j = \Gamma^i{}_{0j}$. -/
theorem classical_christoffel_form (Γ : Conn) (hΓ : IsClassical Γ) :
    (∀ x b c, Γ x 0 b c = 0) ∧
    (∀ x i j k, i ≠ 0 → j ≠ 0 → k ≠ 0 → Γ x i j k = 0) ∧
    (∀ x i j, i ≠ 0 → j ≠ 0 → Γ x i 0 j + Γ x j 0 i = 0) := by sorry

end NewtonCartan
