-- Prove2me | Theorems.Thm_KochHF_slater_one_body_density
-- name    : KochHF.slater_one_body_density
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:26.85704+00:00
-- url     : https://prove2.me/theorems/c66d927a-7b6f-42ff-ac80-da6b712776d2
-- title:
--   One-body density matrix of a Slater determinant is the occupied projector (Eq. (43))
-- statement:
--   Let $\alpha_1,\dots,\alpha_N\in\mathbb C^K$ be orthonormal, $|\Phi\rangle=c^\dagger_{\alpha_N}\cdots c^\dagger_{\alpha_1}|0\rangle$ and $P=\sum_n|\alpha_n\rangle\langle\alpha_n|$. For all reference orbitals $\phi_n,\phi_m$,
--   $$\Gamma^{(1)}_{nm}=\langle\Phi|c^\dagger_n c_m|\Phi\rangle=\langle\phi_m|P|\phi_n\rangle .$$
--
--   As an operator on the one-electron space the one-body density matrix of a Slater determinant is therefore the projector onto the occupied subspace.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 2.4, p. 2.12, Eq. (43).

import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem slater_one_body_density {K N : ℕ} (α : Fin N → Fin K → ℂ)
    (hα : ∀ i j, orbInner (α i) (α j) = if i = j then 1 else 0) (n m : Fin K) :
    matEl (slater α) (cdag n * cann m) (slater α) =
      orbInner (Pi.single m 1) (occProj α (Pi.single n 1)) := by sorry

end KochHF
