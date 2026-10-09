-- Prove2me | Theorems.Thm_OCB2012_prob_nonneg
-- name    : OCB2012.prob_nonneg
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-08T23:11:58.578997+00:00
-- url     : https://prove2.me/theorems/cb3c819d-0d7e-464d-8910-e782eb294fbd
-- title:
--   Non-negativity of the probabilities $\mathrm{Tr}[W(M^{A}\otimes M^{B})]$ for positive $W$
-- statement:
--   Let $A_1, A_2, B_1, B_2$ be finite-dimensional systems (Alice's input and output, Bob's input and output). Let $W^{A_1A_2B_1B_2}\ge 0$ be a positive semidefinite operator, and let $M^{A_1A_2}\ge 0$ and $M^{B_1B_2}\ge 0$ be positive semidefinite operators, for example the Choi–Jamiołkowski (CJ) matrices of completely positive maps. Then the generalized Born-rule expression of Eq. (3) is a non-negative real number:
--
--   $$0 \;\le\; \mathrm{Tr}\!\left[W^{A_1A_2B_1B_2}\left(M^{A_1A_2}\otimes M^{B_1B_2}\right)\right].$$
--
--   This is the content of the label *non-negative probabilities* attached to condition (4) on p. 4: positivity of $W$ guarantees that every pair of CP-map outcomes receives a non-negative probability. It is the basic positivity step in any bound on success probabilities computed from process matrices.
--
--   **Formalization Note.** The order on $\mathbb C$ is `ComplexOrder`, so $0\le z$ means that $z$ is real and non-negative. `prob W MA MB` is `(W * (MA ⊗ₖ MB)).trace`.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 4, Eqs. (3)-(4) ('non-negative probabilities')

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem prob_nonneg {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : W.PosSemidef)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (hA : MA.PosSemidef)
    (MB : Matrix (b1 × b2) (b1 × b2) ℂ) (hB : MB.PosSemidef) :
    0 ≤ prob W MA MB := by sorry

end OCB2012
