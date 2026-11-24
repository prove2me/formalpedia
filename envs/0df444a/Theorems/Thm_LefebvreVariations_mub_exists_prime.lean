-- Prove2me | Theorems.Thm_LefebvreVariations_mub_exists_prime
-- name    : LefebvreVariations.mub_exists_prime
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:23:12.636008+00:00
-- url     : https://prove2.me/theorems/03cd303a-3017-4668-9e33-1a868b87f3a5
-- title:
--   Lefebvre's variations: complete sets of mutually unbiased bases in prime dimension
-- statement:
--   This is the prime case of the existence of complete sets of mutually unbiased bases.
--
--   Let $p$ be a prime. There are $p+1$ orthonormal bases $\mathcal B_0,\dots,\mathcal B_p$ of $\mathbb C^p$ that are pairwise mutually unbiased: for $u\in\mathcal B_i$ and $v\in\mathcal B_j$ with $i\neq j$,
--
--   $$
--   |\langle u,v\rangle|^2=\frac1p .
--   $$
--
--   For odd $p$ one may take the standard basis together with the bases $\{v_{a,b}\}_{b}$, $a\in\mathbb Z/p\mathbb Z$, where $v_{a,b}(x)=p^{-1/2}\,\omega^{ax^2+bx}$ and $\omega=e^{2\pi i/p}$; unbiasedness reduces to the quadratic Gauss sum identity $\big|\sum_x\omega^{cx^2+dx}\big|^2=p$ for $c\neq0$. For $p=2$ the eigenbases of the three Pauli matrices work.
--
--   The number $d+1$ is the maximum possible in dimension $d$, and complete sets are known in every prime-power dimension; whether they exist in other dimensions (already $d=6$) is open. This settles the prime case in the platform's formulation.
--
--   **Formalization Note** Bases and unbiasedness are the mission's `DesignTest.PureVec` and `DesignTest.IsMUBFamily`; the family is indexed by `Fin (p+1)` and each basis by `Fin p`.
-- source:
--   I. D. Ivanović, Geometrical description of quantal state determination, J. Phys. A 14 (1981), 3241–3245 (p + 1 mutually unbiased bases in prime dimension p); W. K. Wootters and B. D. Fields, Optimal state-determination by mutually unbiased measurements, Ann. Physics 191 (1989), 363–381 (prime-power dimensions). Parent problem: DesignTest.mub_exists_prime_power (complete sets of mutually unbiased bases).

import Mathlib
import Definitions.Def_DesignTest_IsMUBFamily

set_option autoImplicit false

namespace LefebvreVariations

/-- **Complete sets of mutually unbiased bases in prime dimension** (Ivanović, *J. Phys. A* 14
(1981) 3241–3245, for odd primes; Wootters–Fields, *Ann. Physics* 191 (1989) 363–381, §3, for
prime powers; the `p + 1` bases are the standard basis and the `p` bases
`v_{a,b} = p^{-1/2} (ω^{b j² + a j})_j`, `ω = exp(2πi/p)`). The prime case of
`DesignTest.mub_exists_prime_power`; for `p = 2` the three bases are the Pauli eigenbases. -/
theorem mub_exists_prime (p : ℕ) (hp : p.Prime) :
    ∃ B : Fin (p + 1) → Fin p → DesignTest.PureVec p, DesignTest.IsMUBFamily B := by
  sorry

end LefebvreVariations
