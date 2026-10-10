-- Prove2me | Theorems.Thm_KochHF_koopmans_theorem
-- name    : KochHF.koopmans_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:09.430048+00:00
-- url     : https://prove2.me/theorems/88dd7fbe-e797-4306-ad32-8fdeda007fc4
-- title:
--   Koopmans' theorem: removing an electron costs $-\varepsilon_a$ (Eq. (66))
-- statement:
--   With $\hat H$, $T$, $U$ as in the definition file and $U_{nn',mm'}=U_{n'n,m'm}$, let $S$ be the occupied reference orbitals and $a\in S$. Removing the electron from orbital $a$ changes the energy expectation value by minus the Hartree-Fock orbital energy:
--   $$\langle S\setminus\{a\}|\hat H|S\setminus\{a\}\rangle-\langle S|\hat H|S\rangle=-\varepsilon_a,\qquad \varepsilon_a=T_{aa}+\sum_{m'\in S}\Delta_{am'} .$$
--
--   Neglecting orbital relaxation, $-\varepsilon_a$ is thus the ionization energy from orbital $a$.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 3.2, p. 2.18, Eqs. (65), (66).

import Mathlib
import Definitions.Def_KochHF_FockSpace
import Definitions.Def_KochHF_Hamiltonian

open Matrix

namespace KochHF

theorem koopmans_theorem {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ)
    (U : Fin K → Fin K → Fin K → Fin K → ℂ) (hU : ∀ n n' m m', U n n' m m' = U n' n m' m)
    (S : Finset (Fin K)) (a : Fin K) (ha : a ∈ S) :
    detEnergy T U (S.erase a) - detEnergy T U S = -hfOrbitalEnergy T U S a := by sorry

end KochHF
