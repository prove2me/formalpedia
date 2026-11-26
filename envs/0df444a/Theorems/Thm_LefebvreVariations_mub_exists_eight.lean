-- Prove2me | Theorems.Thm_LefebvreVariations_mub_exists_eight
-- name    : LefebvreVariations.mub_exists_eight
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:45:30.673583+00:00
-- url     : https://prove2.me/theorems/1e2c42bf-84f3-4b76-9b15-c56f6e216a5b
-- title:
--   Lefebvre's variations, No. 53 — on a theme by Wootters and Fields: a complete set of nine mutually unbiased bases of C^8 exists
-- statement:
--   There exist nine orthonormal bases $B_0,\dots,B_8$ of $\mathbb{C}^8$, each $B_r=(b^r_0,\dots,b^r_7)$, that are pairwise mutually unbiased:
--   $$
--   \bigl|\langle b^r_i,\,b^s_j\rangle\bigr|^2=\frac18\qquad\text{for all } r\ne s \text{ and all } i,j\in\{0,\dots,7\}.
--   $$
--   That is, a complete set of $d+1=9$ mutually unbiased bases of $\mathbb{C}^d$ exists for $d=8=2^3$.
--
--   This is the case $d=8$ of the existence of complete sets of mutually unbiased bases in every prime-power dimension (Wootters–Fields). It is the first prime-power dimension that is neither a prime nor $4$; the construction over the field $\mathbb{F}_8$ (equivalently over the Galois ring $\mathrm{GR}(4,3)$) produces bases whose entries are $\tfrac1{\sqrt8}$ times a fourth root of unity.
--
--   **Formalization Note** The statement is `∃ B : Fin 9 → Fin 8 → PureVec 8, IsMUBFamily B`, using the platform definition `DesignTest.IsMUBFamily` (every `B r` is an `Orthonormal` family in `EuclideanSpace ℂ (Fin 8)` and `‖inner (B r i) (B s j)‖ ^ 2 = 1 / 8` for `r ≠ s`); `PureVec 8` is the platform type of unit vectors of `ℂ^8`.
--
--   **Why this is a variation.** Variation on the open problem of existence of complete sets of mutually unbiased bases (the platform's MUB family, whose open cases include dimension 6). It is the case d = 8, the first prime-power dimension that is neither a prime nor 4, with the parent's own definition IsMUBFamily; an explicit construction here is a model for other dimensions.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   W. K. Wootters and B. D. Fields, Optimal state-determination by mutually unbiased measurements, Ann. Physics 191 (1989) 363-381 (complete sets in prime-power dimension; cited from memory); explicit construction from Galois rings: A. Klappenecker and M. Roetteler, Constructions of mutually unbiased bases, in Finite Fields and Applications, LNCS 2948 (2004) 137-144 (cited from memory). Origin of this statement: the case d = 8 of the platform theorem DesignTest.mub_exists_prime_power (A. Kawachi, Y. Nakata, Y. Takeuchi, Testing State and Unitary Designs, Corollary 4.17), the first prime-power dimension beyond the cases d = 4 and d prime; the proof is an exact finite computation in the Gaussian integers.

import Mathlib
import Definitions.Def_DesignTest_IsMUBFamily

set_option autoImplicit false

namespace LefebvreVariations

/-- **A complete set of nine mutually unbiased bases of `ℂ⁸`**, the first prime-power dimension beyond
`4` that is not a prime (Wootters–Fields, *Optimal state-determination by mutually unbiased
measurements*, Ann. Physics 191 (1989) 363–381, construction over `GF(8)`; the explicit nine bases come
from the Galois ring `GR(4, 3)`, Klappenecker–Rötteler, *Constructions of mutually unbiased bases*,
Finite Fields and Applications, LNCS 2948 (2004) 137–144, cited from memory). It is the case `d = 8` of
`DesignTest.mub_exists_prime_power`. -/
theorem mub_exists_eight :
    ∃ B : Fin 9 → Fin 8 → DesignTest.PureVec 8, DesignTest.IsMUBFamily B := by
  sorry

end LefebvreVariations
