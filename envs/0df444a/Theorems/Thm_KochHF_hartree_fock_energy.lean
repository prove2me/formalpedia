-- Prove2me | Theorems.Thm_KochHF_hartree_fock_energy
-- name    : KochHF.hartree_fock_energy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:35.854987+00:00
-- url     : https://prove2.me/theorems/12a031e9-80d1-4c56-916a-da683cc68cd8
-- title:
--   Energy of a Slater determinant (Hartree-Fock energy, Sec. 3.2)
-- statement:
--   With $\hat H$, $T$, $U$ as in the definition file and $U_{nn',mm'}=U_{n'n,m'm}$, the energy of the determinant $|S\rangle$ of occupied reference orbitals $S$ is
--   $$\langle S|\hat H|S\rangle=\sum_{m\in S}\Bigl(T_{mm}+\sum_{m'\in S,\,m'<m}\Delta_{mm'}\Bigr)=\sum_{m\in S}\Bigl(T_{mm}+\tfrac12\sum_{m'\in S}\Delta_{mm'}\Bigr),$$
--   where $\Delta_{mm'}=U_{mm',mm'}-U_{mm',m'm}$.
--
--   This is the Hartree-Fock total energy expressed through direct and exchange integrals of the occupied orbitals.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 3.2, p. 2.18, Eq. (65) and the displayed Hartree-Fock energy following it; symmetry from Sec. 2.3.2, p. 2.11.

import Mathlib
import Definitions.Def_KochHF_FockSpace
import Definitions.Def_KochHF_Hamiltonian

open Matrix

namespace KochHF

theorem hartree_fock_energy {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ)
    (U : Fin K → Fin K → Fin K → Fin K → ℂ) (hU : ∀ n n' m m', U n n' m m' = U n' n m' m)
    (S : Finset (Fin K)) :
    detEnergy T U S = ∑ m ∈ S, (T m m + ∑ m' ∈ S.filter (· < m), hfDelta U m m') ∧
    detEnergy T U S = ∑ m ∈ S, (T m m + (1 / 2 : ℂ) * ∑ m' ∈ S, hfDelta U m m') := by sorry

end KochHF
