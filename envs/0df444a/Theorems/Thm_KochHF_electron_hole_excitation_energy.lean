-- Prove2me | Theorems.Thm_KochHF_electron_hole_excitation_energy
-- name    : KochHF.electron_hole_excitation_energy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:29.576182+00:00
-- url     : https://prove2.me/theorems/5db90538-7337-476b-b323-383dd540d288
-- title:
--   Electron-hole excitation energy $\varepsilon_b-\varepsilon_a-\Delta_{ab}$ (Eq. (67))
-- statement:
--   With $\hat H$, $T$, $U$ as in the definition file and $U_{nn',mm'}=U_{n'n,m'm}$, let $S$ be the occupied reference orbitals, $a\in S$ and $b\notin S$. The energy of the determinant with an electron moved from $a$ to $b$ satisfies
--   $$\langle S_{a\to b}|\hat H|S_{a\to b}\rangle-\langle S|\hat H|S\rangle=\varepsilon_b-\varepsilon_a-\Delta_{ab},\qquad S_{a\to b}=(S\setminus\{a\})\cup\{b\},$$
--   with $\varepsilon_m=T_{mm}+\sum_{m'\in S}\Delta_{mm'}$ the orbital energies of $S$.
--
--   The term $-\Delta_{ab}$ is the electron-hole interaction of the unrelaxed particle-hole excitation.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 3.2, p. 2.18, Eq. (67).

import Mathlib
import Definitions.Def_KochHF_FockSpace
import Definitions.Def_KochHF_Hamiltonian

open Matrix

namespace KochHF

theorem electron_hole_excitation_energy {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ)
    (U : Fin K → Fin K → Fin K → Fin K → ℂ) (hU : ∀ n n' m m', U n n' m m' = U n' n m' m)
    (S : Finset (Fin K)) (a b : Fin K) (ha : a ∈ S) (hb : b ∉ S) :
    detEnergy T U (insert b (S.erase a)) - detEnergy T U S =
      hfOrbitalEnergy T U S b - hfOrbitalEnergy T U S a - hfDelta U a b := by sorry

end KochHF
