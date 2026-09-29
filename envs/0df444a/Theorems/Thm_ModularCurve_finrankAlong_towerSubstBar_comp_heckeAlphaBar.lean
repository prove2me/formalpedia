-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar
-- name    : ModularCurve.finrankAlong_towerSubstBar_comp_heckeAlphaBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/0fa28acd-658b-5a55-bf57-9997aa1c2642
-- title:
--   Degree of the diagonal in the Hecke exchange square
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $N$ be a nonzero natural number, let $\ell,\ell'$ be primes with $\ell \neq \ell'$, and let $M$ be a nonzero natural number with $M = N\ell\ell'$. For a level $n$, write $F^{\mathrm{full}}_n$ for the subfield $\mathbb{Q}(\mathrm{divisorExpansions}\,n)$ of $\mathbb{Q}((q))$ and $L\cdot F^{\mathrm{full}}_n$ for `laurentBaseChange`, the subfield of $L((q))$ generated over $L$ by the coefficientwise image of $F^{\mathrm{full}}_n$. Three $L$-algebra maps enter: `heckeAlphaBar L N ℓ'`, the inclusion $L\cdot F^{\mathrm{full}}_{N} \hookrightarrow L\cdot F^{\mathrm{full}}_{N\ell'}$; `heckeBetaBar L N ℓ`, the substitution $q \mapsto q^{\ell}$ (the exponent-scaling map `qExpand`) from $L\cdot F^{\mathrm{full}}_{N}$ into $L\cdot F^{\mathrm{full}}_{N\ell}$; and `towerSubstBar L (N*ℓ') ℓ`, the same substitution $q\mapsto q^{\ell}$ out of $L\cdot F^{\mathrm{full}}_{N\ell'}$ followed by the inclusion of $L\cdot F^{\mathrm{full}}_{N\ell'\ell}$ into $L\cdot F^{\mathrm{full}}_{M}$, using the divisibility $N\ell'\ell \mid M$ coming from $hM$. The assertion is an equality of degrees, where `finrankAlong` of an algebra map $\varphi\colon F \to F'$ means the rank of $F'$ as a module over $F$ via $\varphi$: the degree of `heckeAlphaBar L N ℓ'` followed by `towerSubstBar L (N*ℓ') ℓ` equals the degree of `heckeAlphaBar L N ℓ'` times the degree of `heckeBetaBar L N ℓ` — the latter taken at level $N$, not at level $N\ell'$.
--
--   This is the degree computation along the diagonal of the exchange square of degeneracy and substitution maps through level $N\ell\ell'$, the function-field counterpart of the fibre square used to compare the Hecke correspondences $T_\ell$ and $T_{\ell'}$ on $X_0(N)$. It supplies the degree hypothesis of [`ModularCurve.heckeExchangeAt_of_primes_of_ne`](thm.html#ModularCurve.heckeExchangeAt_of_primes_of_ne) and, through it, of [`ModularCurve.heckeOperatorsCommuteBar`](thm.html#ModularCurve.heckeOperatorsCommuteBar); no statement about operators on divisors is made here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean

import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.finrankAlong_towerSubstBar_comp_heckeAlphaBar (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ ℓ' M : ℕ) [hl : Fact (Nat.Prime ℓ)] [hl' : Fact (Nat.Prime ℓ')] [NeZero M] (hM : M = N * ℓ * ℓ') (hne : ℓ ≠ ℓ') : AlgebraicCurve.finrankAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp (heckeAlphaBar L N ℓ')) = AlgebraicCurve.finrankAlong L (heckeAlphaBar L N ℓ') * AlgebraicCurve.finrankAlong L (heckeBetaBar L N ℓ) := by sorry
