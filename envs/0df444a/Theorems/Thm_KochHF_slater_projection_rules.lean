-- Prove2me | Theorems.Thm_KochHF_slater_projection_rules
-- name    : KochHF.slater_projection_rules
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:24:56.825879+00:00
-- url     : https://prove2.me/theorems/5c5d4427-5d5d-4e04-9d2f-754544012d9e
-- title:
--   Annihilators see only the occupied part, creators only the virtual part (Eq. (42))
-- statement:
--   Let $\alpha_1,\dots,\alpha_N\in\mathbb C^K$ be orthonormal, $|\Phi\rangle=c^\dagger_{\alpha_N}\cdots c^\dagger_{\alpha_1}|0\rangle$ and $P=\sum_n|\alpha_n\rangle\langle\alpha_n|$ the projection onto the occupied space (Eq. (41)). Then for every orbital $\varphi$
--   $$c_{\varphi}|\Phi\rangle=c_{P\varphi}|\Phi\rangle\qquad\text{and}\qquad c^\dagger_{\varphi}|\Phi\rangle=c^\dagger_{(1-P)\varphi}|\Phi\rangle .$$
--
--   This is the basic tool for evaluating matrix elements of Slater determinants: annihilating a virtual orbital, or creating an occupied one, gives zero.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 2.4, p. 2.12, Eqs. (41), (42).

import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem slater_projection_rules {K N : ℕ} (α : Fin N → Fin K → ℂ)
    (hα : ∀ i j, orbInner (α i) (α j) = if i = j then 1 else 0) (φ : Fin K → ℂ) :
    cannOrb φ *ᵥ slater α = cannOrb (occProj α φ) *ᵥ slater α ∧
    cdagOrb φ *ᵥ slater α = cdagOrb (φ - occProj α φ) *ᵥ slater α := by sorry

end KochHF
