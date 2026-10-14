-- Prove2me | Theorems.Thm_Giddings1999_boundary_S_matrix_eq_CFT_correlator
-- name    : Giddings1999.boundary_S_matrix_eq_CFT_correlator
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T01:52:15.766507+00:00
-- url     : https://prove2.me/theorems/886ede48-8140-4018-91d0-55e14d62c93f
-- title:
--   Eqs. (23), (42)–(44): the boundary S matrix equals the integrated CFT correlator
-- statement:
--   Let $(X,dV)$ (the bulk) and $(B,db)$ (the boundary) be $\sigma$-finite measure spaces. Let $K=G_{B\partial}:B\times X\to\mathbb C$ be a bulk–boundary kernel, $G_T:X^N\to\mathbb C$ a truncated $N$-point bulk Green function, $Z_1,\dots,Z_N\in\mathbb C$ wave-function renormalizations, and $f_1,\dots,f_N:B\to\mathbb C$ boundary wave-packet profiles. Write $\phi_f(x)=\int db\,f(b)K(b,x)$ (eq. 23). Assume that the CFT correlator is given by Witten's formula (43),
--   $$\Bigl\langle T\prod_a\mathcal O(b_a)\Bigr\rangle=\int\prod_a\bigl[dV_a\,K(b_a,x_a)\bigr]\,G_T(x_1,\dots,x_N),$$
--   and that $(b,x)\mapsto\prod_a f_a(b_a)K(b_a,x_a)\,G_T(x)$ is integrable on $B^N\times X^N$. Then the LSZ expression (42) equals the integrated correlator (44):
--   $$\int\prod_a\Bigl[dV_a\,\frac{\phi_{f_a}(x_a)}{Z_a}\Bigr]G_T(x_1,\dots,x_N)=\int\prod_a\Bigl[db_a\,\frac{f_a(b_a)}{Z_a}\Bigr]\Bigl\langle T\prod_a\mathcal O(b_a)\Bigr\rangle .$$
--
--   This is the paper's final step: the boundary S matrix is given directly by CFT correlators.
--
--   **Formalization Note** The right-hand side of the LSZ formula (42) is taken as the definition of the boundary S matrix, because the operator-level derivation of eqs. (24)–(42) is not rigorous mathematics. In- and out-packets are listed together as $f_1,\dots,f_N$, and the plane-wave limit (45) is not formalized.
-- source:
--   S. B. Giddings, Boundary S matrix and the anti-de Sitter space to conformal field theory dictionary, Phys. Rev. Lett. 83, 2707 (1999), https://doi.org/10.1103/PhysRevLett.83.2707, eqs. (23), (42), (43), (44), p. 2708–2710

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology

namespace Giddings1999

/-- **Milestone, eqs. (23), (42)–(44)**: if the CFT correlator is given by Witten's formula (43),
`⟨T ∏ₐ O(bₐ)⟩ = ∫ ∏ₐ [dVₐ G_{B∂}(bₐ, xₐ)] ⟨0|T ∏ₐ F(xₐ)|0⟩_T`, then the LSZ expression (42) for the
boundary S matrix with the wave packets (23) equals `∫ ∏ₐ [dbₐ fₐ(bₐ)/Zₐ] ⟨T ∏ₐ O(bₐ)⟩` (eq. 44). -/
theorem boundary_S_matrix_eq_CFT_correlator {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    {N : ℕ} (dV : MeasureTheory.Measure X) (db : MeasureTheory.Measure B)
    [MeasureTheory.SigmaFinite dV] [MeasureTheory.SigmaFinite db]
    (K : B → X → ℂ) (Z : Fin N → ℂ) (f : Fin N → B → ℂ) (GT : (Fin N → X) → ℂ)
    (CFT : (Fin N → B) → ℂ)
    (hWitten : ∀ b : Fin N → B, CFT b =
      ∫ x, (∏ a, K (b a) (x a)) * GT x ∂(MeasureTheory.Measure.pi fun _ => dV))
    (hint : MeasureTheory.Integrable
      (fun p : (Fin N → B) × (Fin N → X) => (∏ a, f a (p.1 a) * K (p.1 a) (p.2 a)) * GT p.2)
      ((MeasureTheory.Measure.pi fun _ => db).prod (MeasureTheory.Measure.pi fun _ => dV))) :
    lszBoundarySMatrix dV db K Z f GT =
      ∫ b, (∏ a, f a (b a) / Z a) * CFT b ∂(MeasureTheory.Measure.pi fun _ => db) := by
  sorry

end Giddings1999
