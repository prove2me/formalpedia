-- Prove2me | Theorems.Thm_ModularCurve_eisensteinIdeal_smul_cuspidalClass
-- name    : ModularCurve.eisensteinIdeal_smul_cuspidalClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/19834da4-ffb9-575b-837f-2eee65a08bb2
-- title:
--   The Eisenstein ideal annihilates the cuspidal class
-- statement:
--   Let $p$ be a natural number carrying the instance `Fact p.Prime`. Write `HeckeAlg` for the polynomial ring $\mathbb{Z}[X_\ell : \ell \text{ prime}]$ (formally `MvPolynomial Nat.Primes ℤ`), and let `eisensteinIdeal p` be the kernel of the $\mathbb{Z}$-algebra map `HeckeAlg → ℤ` sending the variable indexed by a prime $\ell$ to `eisensteinSystem p ℓ`, that is to $1$ when $\ell \mid p$ and to $1 + \ell$ otherwise. Let `JZero p` be the group `Pic0` of degree-zero divisor classes of the function field `modularFunctionFieldBar p` over $\overline{\mathbb{Q}}$, i.e. degree-zero divisors modulo principal ones, and let `cuspidalClass p` be the class of the divisor $(\mathrm{cusp}_0) - (\mathrm{cusp}_\infty)$, the difference of the two cusps `cuspZeroBar p` and `cuspInftyBar p` with coefficients $1$ and $-1$. Equip `JZero p` with the `HeckeAlg`-module structure `heckeModuleBar p`, which is restriction of scalars along `heckeEvalBar` (variables acting as the Hecke operators `heckeOperatorBar p ℓ`) when these operators commute, and along evaluation at $0$ otherwise. The assertion is that every $i$ belonging to `eisensteinIdeal p` satisfies $i \cdot \mathrm{cuspidalClass}\, p = 0$ for this module structure.
--
--   This is the statement that the Eisenstein ideal annihilates the cuspidal class $[(0)-(\infty)]$ in the Jacobian of the modular curve of level $p$, as in Mazur's study of the Eisenstein ideal. It is used in the derivation of the congruence between the $q$-expansion coefficients of a cusp form and the divisor-sum coefficients of the relevant Eisenstein series, recorded as [`CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator`](thm.html#CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eisensteinIdeal_smul_cuspidalClass.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_Eisenstein

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.eisensteinIdeal_smul_cuspidalClass (p : ℕ) [Fact p.Prime] : ∀ i ∈ eisensteinIdeal p, (letI := heckeModuleBar p; i • cuspidalClass p) = 0 := by sorry
