-- Prove2me | Theorems.Thm_KochHF_fock_matrix_single_excitation
-- name    : KochHF.fock_matrix_single_excitation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:47.470422+00:00
-- url     : https://prove2.me/theorems/03ea7fbf-e4cb-4937-a7cc-3bd0d552436b
-- title:
--   Single-excitation matrix elements of $\hat H$ are Fock-matrix entries (Eq. (64))
-- statement:
--   Let $\hat H=\sum_{n,m}c^\dagger_nT_{nm}c_m+\sum_{n>n',m>m'}c^\dagger_nc^\dagger_{n'}(U_{nn',mm'}-U_{nn',m'm})c_{m'}c_m$ with two-body matrix elements satisfying the exchange symmetry $U_{nn',mm'}=U_{n'n,m'm}$ (Sec. 2.3.2). Let $|S\rangle$ be the determinant of the occupied reference orbitals $S$. Then for every virtual $n\notin S$ and occupied $m\in S$,
--   $$\langle S|\,c^\dagger_m c_n\,\hat H\,|S\rangle=F_{nm}=T_{nm}+\sum_{m'\in S}\bigl(U_{nm',mm'}-U_{nm',m'm}\bigr).$$
--
--   So for this Hamiltonian the Brillouin condition says exactly that the occupied–virtual block of the Fock matrix vanishes; this is why Hartree-Fock reduces to a self-consistent one-body problem.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 3.2, pp. 2.17–2.18, Hamiltonian preceding Eq. (64) and Eq. (64); symmetry $M_{nn',mm'}=M_{n'n,m'm}$ from Sec. 2.3.2, p. 2.11.

import Mathlib
import Definitions.Def_KochHF_FockSpace
import Definitions.Def_KochHF_Hamiltonian

open Matrix

namespace KochHF

theorem fock_matrix_single_excitation {K : ℕ} (T : Matrix (Fin K) (Fin K) ℂ)
    (U : Fin K → Fin K → Fin K → Fin K → ℂ) (hU : ∀ n n' m m', U n n' m m' = U n' n m' m)
    (S : Finset (Fin K)) (n m : Fin K) (hn : n ∉ S) (hm : m ∈ S) :
    matEl (basisState S) (cdag m * cann n * hamiltonian T U) (basisState S) =
      fockMatrix T U S n m := by sorry

end KochHF
