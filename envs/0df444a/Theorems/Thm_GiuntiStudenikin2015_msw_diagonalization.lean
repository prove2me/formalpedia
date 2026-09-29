-- Prove2me | Theorems.Thm_GiuntiStudenikin2015_msw_diagonalization
-- name    : GiuntiStudenikin2015.msw_diagonalization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T14:26:51.261561+00:00
-- url     : https://prove2.me/theorems/20fae0d6-c71a-4ffe-9557-52880ce3cfa1
-- title:
--   Diagonalization of the MSW Hamiltonian in matter
-- statement:
--   Let $\Delta m^2,V_{\rm CC}\in\mathbb R$, $0\le\vartheta\le\pi/2$ and $E>0$. Let $\mathrm H$ be the effective two-neutrino Hamiltonian in matter (2.46) with $A_{\rm CC}=2EV_{\rm CC}$, $\Delta m^2_{\rm M}$ the effective squared-mass difference (2.53), and $\vartheta_{\rm M}$ the effective mixing angle, characterized by $\Delta m^2_{\rm M}\cos2\vartheta_{\rm M}=\Delta m^2\cos2\vartheta-2EV_{\rm CC}$, $\Delta m^2_{\rm M}\sin2\vartheta_{\rm M}=\Delta m^2\sin2\vartheta$ (equivalent to (2.54)). With $U_{\rm M}=\begin{pmatrix}\cos\vartheta_{\rm M}&\sin\vartheta_{\rm M}\\-\sin\vartheta_{\rm M}&\cos\vartheta_{\rm M}\end{pmatrix}$,
--   $$U_{\rm M}^T\,\mathrm H\,U_{\rm M}=\frac{1}{4E}\operatorname{diag}\bigl(-\Delta m^2_{\rm M},\,\Delta m^2_{\rm M}\bigr).$$
--
--   This identifies the effective massive neutrinos in matter and their squared-mass difference, which govern the MSW effect.
--
--   **Formalization Note** $\vartheta_{\rm M}$ is defined as half the principal argument of $(\Delta m^2\cos2\vartheta-2EV_{\rm CC})+i\,\Delta m^2\sin2\vartheta$, which avoids the division by zero in (2.54) at the resonance (2.55).
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531, p. 537, Sec. II.D, Eqs. (2.46), (2.50)–(2.54)

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

namespace GiuntiStudenikin2015
theorem msw_diagonalization (dm2 θ E Vcc : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2) (hE : 0 < E) :
    Matrix.transpose (twoFlavorMixing (mswMixingAngle dm2 θ E Vcc)) * mswHamiltonian dm2 θ E Vcc *
        twoFlavorMixing (mswMixingAngle dm2 θ E Vcc) =
      ((1 / (4 * E) : ℝ) : ℂ) •
        Matrix.diagonal ![((-mswDeltaM2 dm2 θ E Vcc : ℝ) : ℂ), ((mswDeltaM2 dm2 θ E Vcc : ℝ) : ℂ)] := by
  sorry
end GiuntiStudenikin2015
