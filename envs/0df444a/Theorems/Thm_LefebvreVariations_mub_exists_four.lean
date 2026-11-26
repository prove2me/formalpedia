-- Prove2me | Theorems.Thm_LefebvreVariations_mub_exists_four
-- name    : LefebvreVariations.mub_exists_four
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:42:03.505516+00:00
-- url     : https://prove2.me/theorems/ae516652-c8ce-4ba3-b976-9dd69aaee185
-- title:
--   Lefebvre's variations, No. 27 — on a theme by Wootters and Fields: a complete set of mutually unbiased bases in dimension 4
-- statement:
--   This is the existence of a complete set of mutually unbiased bases in dimension $4$.
--
--   There are five orthonormal bases $\mathcal B_0,\dots,\mathcal B_4$ of $\mathbb C^4$ such that $|\langle u,v\rangle|^2=\frac14$ whenever $u\in\mathcal B_i$, $v\in\mathcal B_j$, $i\neq j$. One may take the standard basis together with four bases whose vectors have all coordinates in $\{\pm1,\pm i\}/2$, the joint eigenbases of the maximal commuting families of two-qubit Pauli operators.
--
--   Complete sets of $d+1$ mutually unbiased bases exist in every prime-power dimension (Wootters–Fields), and their existence in other dimensions is open. Dimension $4$ is the first prime power that is not prime, where the construction requires the field with four elements rather than the integers modulo $d$.
--
--   **Formalization Note** The family is the mission's `DesignTest.IsMUBFamily` on `DesignTest.PureVec 4`, indexed by `Fin 5` and `Fin 4`.
--
--   **Why this is a variation.** This varies the open Prove2Me problem on complete sets of mutually unbiased bases in prime-power dimensions (`DesignTest.mub_exists_prime_power`, the Wootters–Fields theme). It is the case $d=4$: five mutually unbiased bases of $\mathbb C^4$, the first prime-power dimension that is not prime, where the field with four elements is needed instead of the integers modulo $d$. Settling it settles the smallest instance the prime construction does not reach, and gives an explicit family to test the general prime-power statement against.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   W. K. Wootters and B. D. Fields, Optimal state-determination by mutually unbiased measurements, Ann. Physics 191 (1989), 363–381 (complete sets in prime-power dimensions, constructed over GF(p^m)); explicit bases in dimension 4 from two-qubit Pauli operators: S. Bandyopadhyay, P. O. Boykin, V. Roychowdhury and F. Vatan, A new proof for the existence of mutually unbiased bases, Algorithmica 34 (2002), 512–528. Parent problem: DesignTest.mub_exists_prime_power.

import Mathlib
import Definitions.Def_DesignTest_IsMUBFamily

set_option autoImplicit false

namespace LefebvreVariations

/-- **A complete set of five mutually unbiased bases of `ℂ⁴`**, the first non-prime prime-power
dimension `4 = 2²` (Wootters–Fields, *Optimal state-determination by mutually unbiased
measurements*, Ann. Physics 191 (1989) 363–381, §3, construction over `GF(4)`; the explicit
five bases are the joint eigenbases of the five maximal commuting sets of the two-qubit Pauli group,
see Durt–Englert–Bengtsson–Życzkowski, *On mutually unbiased bases*, Int. J. Quantum Inf. 8 (2010)
535–640, §3). It is the case `d = 4` of `DesignTest.mub_exists_prime_power`, the first one that
the prime construction does not reach. -/
theorem mub_exists_four :
    ∃ B : Fin 5 → Fin 4 → DesignTest.PureVec 4, DesignTest.IsMUBFamily B := by
  sorry

end LefebvreVariations
