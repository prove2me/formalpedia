-- Prove2me | Theorems.Thm_KochHF_brillouin_theorem
-- name    : KochHF.brillouin_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:58.190036+00:00
-- url     : https://prove2.me/theorems/5d3d5760-1d93-4c6c-940b-4bd7cf539b18
-- title:
--   Brillouin theorem: stationarity of a Slater determinant ⇔ no single excitations (Eqs. (62), (63))
-- statement:
--   Let $\hat H$ be a hermitian operator on Fock space, $\alpha_1,\dots,\alpha_N\in\mathbb C^K$ orthonormal orbitals and $|\Phi\rangle=c^\dagger_{\alpha_N}\cdots c^\dagger_{\alpha_1}|0\rangle$. For a hermitian $K\times K$ matrix $M$ put $\hat M=\sum_{\alpha\beta}M_{\alpha\beta}c^\dagger_\alpha c_\beta$ and $E_M(\lambda)=\langle\Phi|e^{i\lambda\hat M}\hat He^{-i\lambda\hat M}|\Phi\rangle$. Then the following are equivalent:
--
--   1. **(Stationarity)** for every hermitian $M$, $E_M$ has derivative $0$ at $\lambda=0$;
--   2. **(Brillouin condition)** for every occupied orbital $\varphi_o\in\operatorname{span}\{\alpha_1,\dots,\alpha_N\}$ and every virtual orbital $\varphi_v\perp\alpha_1,\dots,\alpha_N$,
--   $$\langle\Phi|\,c^\dagger_{\varphi_o}c_{\varphi_v}\,\hat H\,|\Phi\rangle=0 .$$
--
--   In words: a Slater determinant is a stationary point of the energy under all one-body unitary variations exactly when the Hamiltonian has no matrix elements between it and its singly excited determinants. This is the variational characterization of Hartree-Fock determinants on which the self-consistent field method rests.
--
--   **Formalization Note** The source states (63) with orthonormal reference orbitals $m\le N$ occupied and $n>N$ virtual; the formal statement quantifies over all occupied and all virtual orbitals, which is the basis-independent form of the same condition.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 3.2, pp. 2.16–2.17, Eqs. (55), (61)–(63) ("the Brillouin theorem").

import Mathlib
import Definitions.Def_KochHF_FockSpace

open Matrix

namespace KochHF

theorem brillouin_theorem {K N : ℕ} (H : FockOp K) (hH : H.IsHermitian)
    (α : Fin N → Fin K → ℂ) (hα : ∀ i j, orbInner (α i) (α j) = if i = j then 1 else 0) :
    (∀ M : Matrix (Fin K) (Fin K) ℂ, M.IsHermitian →
      HasDerivAt
        (fun t : ℝ => matEl (slater α)
          (NormedSpace.exp ((Complex.I * t) • oneBodyOp M) * H *
            NormedSpace.exp ((-(Complex.I * t)) • oneBodyOp M)) (slater α))
        0 0) ↔
    (∀ φo φv : Fin K → ℂ, φo ∈ Submodule.span ℂ (Set.range α) →
      (∀ i, orbInner (α i) φv = 0) →
      matEl (slater α) (cdagOrb φo * cannOrb φv * H) (slater α) = 0) := by sorry

end KochHF
