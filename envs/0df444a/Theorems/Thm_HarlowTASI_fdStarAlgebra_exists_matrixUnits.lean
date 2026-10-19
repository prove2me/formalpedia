-- Prove2me | Theorems.Thm_HarlowTASI_fdStarAlgebra_exists_matrixUnits
-- name    : HarlowTASI.fdStarAlgebra_exists_matrixUnits
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-10T15:20:20.837978+00:00
-- url     : https://prove2.me/theorems/83215c6e-3e19-484c-bfc8-33ed1772cb1a
-- title:
--   Every finite-dimensional von Neumann algebra has a complete system of matrix units
-- statement:
--   Let $M$ be a von Neumann algebra on the finite-dimensional Hilbert space $\mathbb C^{C}$, i.e. a $*$-subalgebra (containing $I$) of the $C\times C$ complex matrices. Then there are a number $N\ge 0$ of blocks, block sizes $d_{r_\alpha}\ge 1$ for $\alpha<N$, and operators $e^{\alpha}_{ij}\in M$ ($\alpha<N$, $0\le i,j<d_{r_\alpha}$) forming a complete system of matrix units:
--   $$e^{\alpha}_{ij}\,e^{\alpha}_{kl}=\delta_{jk}\,e^{\alpha}_{il},\qquad e^{\alpha}_{ij}\,e^{\beta}_{kl}=0\ (\alpha\ne\beta),\qquad (e^{\alpha}_{ij})^\dagger=e^{\alpha}_{ji},\qquad e^{\alpha}_{ii}\neq 0,\qquad \sum_{\alpha}\sum_i e^{\alpha}_{ii}=I,$$
--   and they span $M$:
--   $$M=\Big\{\sum_\alpha\sum_{i,j}x^{\alpha}_{ij}\,e^{\alpha}_{ij}\ :\ x^\alpha\in\mathbb C^{d_{r_\alpha}\times d_{r_\alpha}}\Big\}.$$
--
--   In Harlow's proof, $\alpha$ labels the minimal projections $p_\alpha$ of the center $Z_M$ (Proposition A.7), and inside the factor $p_\alpha M p_\alpha$ one takes a maximal orthogonal family of minimal projections $p_i$ with partial isometries $a_i\in M$, $a_i^\dagger a_i=p_i$, $a_ia_i^\dagger=p_1$; then $e_{ij}=a_i^\dagger a_j$ (proof of Theorem A.5). When $C$ is empty, $N=0$.
-- source:
--   Step in the proof of Theorem 5.1 of D. Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, arXiv:1802.01040, §5.3, p. 44, whose proof is deferred to D. Harlow, The Ryu-Takayanagi Formula from Quantum Error Correction, arXiv:1607.03901, Appendix A.5-A.6, pp. 47-49 (Proposition A.7 and the proof of Theorem A.5: the operators a_i^dagger a_j generate M).

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

namespace HarlowTASI
open Matrix
open scoped Kronecker

theorem fdStarAlgebra_exists_matrixUnits {C : Type} [Fintype C] [DecidableEq C]
    (M : StarSubalgebra ℂ (Matrix C C ℂ)) :
    ∃ (N : ℕ) (dr : Fin N → ℕ) (e : (a : Fin N) → Fin (dr a) → Fin (dr a) → Matrix C C ℂ),
      (∀ a, 0 < dr a) ∧
      (∀ a i j k l, e a i j * e a k l = if j = k then e a i l else 0) ∧
      (∀ a b i j k l, a ≠ b → e a i j * e b k l = 0) ∧
      (∀ a i j, (e a i j)ᴴ = e a j i) ∧
      (∀ a i, e a i i ≠ 0) ∧
      ∑ a, ∑ i, e a i i = 1 ∧
      (M : Set (Matrix C C ℂ)) =
        {X | ∃ x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ,
          X = ∑ a, ∑ i, ∑ j, x a i j • e a i j} := by sorry

end HarlowTASI
