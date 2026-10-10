-- Prove2me | Theorems.Thm_KochHF_slater_wick
-- name    : KochHF.slater_wick
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:04.799509+00:00
-- url     : https://prove2.me/theorems/d4a21a9a-b3db-4639-bc7d-f3271ae80694
-- title:
--   Wick's theorem for Slater determinants: $p$-body density matrices are determinants (Eq. (45))
-- statement:
--   Let $\alpha_1,\dots,\alpha_N\in\mathbb C^K$ be orthonormal and $|\Phi\rangle=c^\dagger_{\alpha_N}\cdots c^\dagger_{\alpha_1}|0\rangle$, with one-body density matrix $\Gamma^{(1)}_{nm}=\langle\Phi|c^\dagger_nc_m|\Phi\rangle$. For every $p\ge0$ and reference indices $n_1,\dots,n_p$, $m_1,\dots,m_p$,
--   $$\langle\Phi|c^\dagger_{n_p}\cdots c^\dagger_{n_1}\,c_{m_1}\cdots c_{m_p}|\Phi\rangle=\det\begin{pmatrix}\Gamma^{(1)}_{n_1m_1}&\cdots&\Gamma^{(1)}_{n_1m_p}\\ \vdots&\ddots&\vdots\\ \Gamma^{(1)}_{n_pm_1}&\cdots&\Gamma^{(1)}_{n_pm_p}\end{pmatrix}.$$
--
--   All higher-order density matrices of a Slater determinant are thus determined by its one-body density matrix; the case $p=2$ is Eq. (44).
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 2.4, pp. 2.12–2.13, Eqs. (44), (45).

import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem slater_wick {K N p : ℕ} (α : Fin N → Fin K → ℂ)
    (hα : ∀ i j, orbInner (α i) (α j) = if i = j then 1 else 0) (n m : Fin p → Fin K) :
    matEl (slater α)
        ((List.ofFn fun i => cdag (n i)).reverse.prod * (List.ofFn fun i => cann (m i)).prod)
        (slater α) =
      (Matrix.of fun i j => matEl (slater α) (cdag (n i) * cann (m j)) (slater α)).det := by sorry

end KochHF
