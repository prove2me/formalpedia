-- Prove2me | Theorems.Thm_LefebvreVariations_mub_exists_nine
-- name    : LefebvreVariations.mub_exists_nine
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:48:37.085794+00:00
-- url     : https://prove2.me/theorems/6b479d74-f9e3-5843-95c4-13940d207f2c
-- title:
--   Lefebvre's variations, No. 69 — on a theme by Wootters and Fields: a complete set of ten mutually unbiased bases of C^9 exists
-- statement:
--   There exist ten orthonormal bases $B_0,\dots,B_9$ of $\mathbb{C}^9$, each $B_r=(b^r_0,\dots,b^r_8)$, that are pairwise mutually unbiased:
--   $$
--   \bigl|\langle b^r_i,\,b^s_j\rangle\bigr|^2=\frac19\qquad\text{for all } r\ne s \text{ and all } i,j\in\{0,\dots,8\}.
--   $$
--   That is, a complete set of $d+1=10$ mutually unbiased bases of $\mathbb{C}^d$ exists for $d=9=3^2$.
--
--   This is the case $d=9$ of the existence of complete sets of mutually unbiased bases in every prime-power dimension (Wootters–Fields). It is the first odd prime-power dimension that is not a prime. The question of whether a complete set exists in dimension $6$, which is not a prime power, remains open.
--
--   **Formalization Note** The statement is `∃ B : Fin 10 → Fin 9 → PureVec 9, IsMUBFamily B`, using the platform definition `DesignTest.IsMUBFamily` (every `B r` is an `Orthonormal` family in `EuclideanSpace ℂ (Fin 9)` and `‖inner (B r i) (B s j)‖ ^ 2 = 1 / 9` for `r ≠ s`); `PureVec 9` is the platform type of unit vectors of $\mathbb{C}^9$.
--
--   **Why this is a variation.** Variation on the open DesignTest.mub_exists_prime_power (complete sets of mutually unbiased bases in prime-power dimension). It is the case d = 9, the first odd prime-power dimension that is not a prime, with the parent's own definition IsMUBFamily; an explicit construction here is a model for other prime-power dimensions.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   W. K. Wootters and B. D. Fields, Optimal state-determination by mutually unbiased measurements, Ann. Physics 191 (1989) 363-381 (complete sets in prime-power dimension; cited from memory, pages not re-checked); explicit constructions by quadratic Gauss sums: Bandyopadhyay, Boykin, Roychowdhury and Vatan, A new proof for the existence of mutually unbiased bases, Algorithmica 34 (2002) 512-528 (cited from memory). Origin of this statement: the case d = 9 of the platform theorem DesignTest.mub_exists_prime_power (Kawachi, Nakata, Takeuchi, Testing State and Unitary Designs, Corollary 4.17), the first odd prime-power dimension that is not a prime.

import Mathlib
import Definitions.Def_DesignTest_IsMUBFamily

set_option autoImplicit false

namespace LefebvreVariations

/-- **A complete set of ten mutually unbiased bases of `ℂ⁹`**, the first odd prime-power dimension that
is not a prime (Wootters–Fields, *Optimal state-determination by mutually unbiased measurements*,
Ann. Physics 191 (1989) 363–381, construction over `GF(9)`; the explicit bases are the quadratic
Gauss-sum bases `x ↦ ω^{Tr(a x² + b x)}/3` over `𝔽₉`, Ivanović 1981 and Bandyopadhyay–Boykin–Roychowdhury–
Vatan, Algorithmica 34 (2002) 512–528, cited from memory). It is the case `d = 9` of
`DesignTest.mub_exists_prime_power`. -/
theorem mub_exists_nine :
    ∃ B : Fin 10 → Fin 9 → DesignTest.PureVec 9, DesignTest.IsMUBFamily B := by
  sorry

end LefebvreVariations
