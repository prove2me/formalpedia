-- Prove2me | Theorems.Thm_KochHF_canonical_anticommutation
-- name    : KochHF.canonical_anticommutation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:23:39.539173+00:00
-- url     : https://prove2.me/theorems/96537681-edc9-48f6-8fb0-6b06cdf7f60b
-- title:
--   Canonical anticommutation relations (Eq. (15))
-- statement:
--   For all orbitals $\varphi,\chi\in\mathbb C^K$ the creation and annihilation operators of Fock space satisfy the defining relations (15):
--   $$(c^\dagger_\varphi)^\dagger=c_\varphi,\qquad \{c_\varphi,c_\chi\}=0=\{c^\dagger_\varphi,c^\dagger_\chi\},\qquad \{c_\varphi,c^\dagger_\chi\}=\langle\varphi|\chi\rangle,$$
--   $$c_\varphi|0\rangle=0,\qquad\langle0|0\rangle=1,$$
--   where $\{A,B\}=AB+BA$ (Eq. (14)).
--
--   These relations are the postulates from which all of second quantization in the source is derived; in the finite model they become a theorem about the explicit operators.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 2.1, p. 2.6, Eqs. (14), (15) (and (16) for general orbitals).

import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem canonical_anticommutation {K : ℕ} (φ χ : Fin K → ℂ) :
    (cdagOrb φ)ᴴ = cannOrb φ ∧
    cannOrb φ * cannOrb χ + cannOrb χ * cannOrb φ = 0 ∧
    cdagOrb φ * cdagOrb χ + cdagOrb χ * cdagOrb φ = 0 ∧
    cannOrb φ * cdagOrb χ + cdagOrb χ * cannOrb φ = orbInner φ χ • (1 : FockOp K) ∧
    cannOrb φ *ᵥ vacuum K = 0 ∧
    fockInner (vacuum K) (vacuum K) = 1 := by sorry

end KochHF
