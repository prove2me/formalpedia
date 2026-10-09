-- Prove2me | Theorems.Thm_OCB2012_W7_isProcessMatrix
-- name    : OCB2012.W7_isProcessMatrix
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-07T23:08:59.606273+00:00
-- url     : https://prove2.me/theorems/43b06d20-3a5d-4dbd-9fca-ad43db40c2b1
-- title:
--   Eq. (7) — a valid four-qubit process matrix
-- statement:
--   On four qubits $A_1A_2B_1B_2$, the matrix
--   $$W=\tfrac14\Big[\mathbb 1+\tfrac1{\sqrt2}\big(\sigma_z^{A_2}\sigma_z^{B_1}+\sigma_z^{A_1}\sigma_x^{B_1}\sigma_z^{B_2}\big)\Big]$$
--   is a **process matrix**: $W\ge 0$ (Eq. (4)), and $\operatorname{Tr}[W(M^{A_1A_2}\otimes M^{B_1B_2})]=1$ for all $M^{A_1A_2},M^{B_1B_2}\ge 0$ with $\operatorname{Tr}_{A_2}M^{A_1A_2}=\mathbb 1^{A_1}$ and $\operatorname{Tr}_{B_2}M^{B_1B_2}=\mathbb 1^{B_1}$ (Eq. (5)).
-- source:
--   O. Oreshkov, F. Costa, Č. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 5, Eq. (7) and the sentence following it; conditions (4)–(5) on p. 4

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem W7_isProcessMatrix : IsProcessMatrix W7 := by sorry

end OCB2012
