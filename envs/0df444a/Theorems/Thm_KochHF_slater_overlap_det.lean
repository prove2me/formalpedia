-- Prove2me | Theorems.Thm_KochHF_slater_overlap_det
-- name    : KochHF.slater_overlap_det
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:24:12.34748+00:00
-- url     : https://prove2.me/theorems/b2718ad6-be09-44b6-b551-c082f4993394
-- title:
--   Overlap of Slater determinants is the determinant of orbital overlaps (Eqs. (7), (46))
-- statement:
--   Let $\alpha_1,\dots,\alpha_N$ and $\beta_1,\dots,\beta_N$ be arbitrary orbitals in $\mathbb C^K$ and $|\Phi_\alpha\rangle=c^\dagger_{\alpha_N}\cdots c^\dagger_{\alpha_1}|0\rangle$, $|\Phi_\beta\rangle$ likewise. Then
--   $$\langle\Phi_\alpha|\Phi_\beta\rangle=\det\begin{pmatrix}\langle\alpha_1|\beta_1\rangle&\cdots&\langle\alpha_1|\beta_N\rangle\\ \vdots&\ddots&\vdots\\ \langle\alpha_N|\beta_1\rangle&\cdots&\langle\alpha_N|\beta_N\rangle\end{pmatrix}.$$
--
--   In particular, Slater determinants built from orthonormal orbitals are normalized, and determinants of orthonormal basis orbitals form an orthonormal basis.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 1, p. 2.4, Eq. (7); Sec. 2.4, p. 2.13, Eq. (46).

import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem slater_overlap_det {K N : ℕ} (α β : Fin N → Fin K → ℂ) :
    fockInner (slater α) (slater β) = (Matrix.of fun i j => orbInner (α i) (β j)).det := by sorry

end KochHF
