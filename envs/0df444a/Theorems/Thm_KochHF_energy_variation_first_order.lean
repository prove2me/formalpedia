-- Prove2me | Theorems.Thm_KochHF_energy_variation_first_order
-- name    : KochHF.energy_variation_first_order
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:09.735316+00:00
-- url     : https://prove2.me/theorems/258a1c92-71a8-4e32-ba1f-76217e757d43
-- title:
--   First-order energy variation under $e^{i\lambda\hat M}$ (Eqs. (61), (62))
-- statement:
--   Let $\hat H$ be any operator on Fock space, $|\Phi\rangle=c^\dagger_{\alpha_N}\cdots c^\dagger_{\alpha_1}|0\rangle$ a Slater determinant, $M$ a hermitian $K\times K$ matrix and
--   $$E(\lambda)=\langle\Phi|e^{i\lambda\hat M}\,\hat H\,e^{-i\lambda\hat M}|\Phi\rangle .$$
--   Then $E$ is differentiable at $\lambda=0$ with
--   $$E'(0)=i\,\langle\Phi|[\hat M,\hat H]|\Phi\rangle .$$
--   Hence the energy functional is stationary under all such variations exactly when $\langle\Phi|[\hat H,\hat M]|\Phi\rangle=0$ for every hermitian $M$ (Eq. (62)).
--
--   **Formalization Note** The source's Eq. (61) prints the first-order term as $i\lambda\langle\Phi|[\hat H,\hat M]|\Phi\rangle$; differentiating $e^{i\lambda\hat M}\hat He^{-i\lambda\hat M}$ gives $i[\hat M,\hat H]=-i[\hat H,\hat M]$. The statement uses the correct sign; the stationarity condition (62) is unaffected.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 3.2, p. 2.17, Eqs. (61), (62).

import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem energy_variation_first_order {K N : ℕ} (H : FockOp K) (α : Fin N → Fin K → ℂ)
    (M : Matrix (Fin K) (Fin K) ℂ) (hM : M.IsHermitian) :
    HasDerivAt
      (fun t : ℝ => matEl (slater α)
        (NormedSpace.exp ((Complex.I * t) • oneBodyOp M) * H *
          NormedSpace.exp ((-(Complex.I * t)) • oneBodyOp M)) (slater α))
      (Complex.I * matEl (slater α) (oneBodyOp M * H - H * oneBodyOp M) (slater α)) 0 := by sorry

end KochHF
