-- Prove2me | Theorems.Thm_GiuntiStudenikin2015_mixing_matrix_unitary
-- name    : GiuntiStudenikin2015.mixing_matrix_unitary
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T13:06:07.586981+00:00
-- url     : https://prove2.me/theorems/4c7ec7e5-e143-4041-9e1f-9fa73c863c93
-- title:
--   Unitarity of the standard mixing matrix $U^{\mathrm D}D^{\mathrm M}$
-- statement:
--   Let $\vartheta_{12},\vartheta_{13},\vartheta_{23}\in[0,\pi/2]$, $\delta_{13}\in[0,2\pi)$ and $\lambda_{21},\lambda_{31}\in\mathbb R$. Let $U^{\mathrm D}=U^{\mathrm D}(\vartheta_{12},\vartheta_{13},\vartheta_{23},\delta_{13})$ be the standard parametrization (2.27) and $D^{\mathrm M}=\operatorname{diag}(1,e^{i\lambda_{21}},e^{i\lambda_{31}})$. Then both
--   $$U^{\mathrm D}\quad\text{and}\quad U=U^{\mathrm D}D^{\mathrm M}$$
--   are unitary $3\times3$ matrices: $UU^\dagger=U^\dagger U=1$.
--
--   This justifies calling (2.26)–(2.28) a parametrization of the three-neutrino mixing matrix, and is the hypothesis under which all oscillation formulas of the mission apply.
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531, p. 535, Sec. II.C, Eqs. (2.26)–(2.28)

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

namespace GiuntiStudenikin2015
theorem mixing_matrix_unitary (θ12 θ13 θ23 δ13 lam21 lam31 : ℝ)
    (h12 : 0 ≤ θ12 ∧ θ12 ≤ Real.pi / 2) (h13 : 0 ≤ θ13 ∧ θ13 ≤ Real.pi / 2)
    (h23 : 0 ≤ θ23 ∧ θ23 ≤ Real.pi / 2) (hδ : 0 ≤ δ13 ∧ δ13 < 2 * Real.pi) :
    diracMixing θ12 θ13 θ23 δ13 ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    diracMixing θ12 θ13 θ23 δ13 * majoranaPhases lam21 lam31 ∈
      Matrix.unitaryGroup (Fin 3) ℂ := by sorry
end GiuntiStudenikin2015
