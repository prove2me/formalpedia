-- Prove2me | Theorems.Thm_ModularCurve_finite_torsionBySet_eisensteinMaximalIdeal_pow
-- name    : ModularCurve.finite_torsionBySet_eisensteinMaximalIdeal_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/0826a816-4b07-5d17-b0ff-bbb4cdf682f3
-- title:
--   Finiteness of Eisenstein P^m-torsion on J₀(p)
-- statement:
--   Let $p$ be a prime, let $q$ be a natural number that is prime, and let $m$ be a natural number. Write `HeckeAlg` for the abstract Hecke algebra, the polynomial ring $\mathbb{Z}[X_\ell]$ in indeterminates indexed by the primes $\ell$, and `JZero p` for the degree-zero part of the divisor class group $\mathrm{Pic}^0$ of the function field `modularFunctionFieldBar p` over $\overline{\mathbb{Q}}$, that is, degree-zero divisors modulo principal divisors, for the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $p$. Give `JZero p` the `HeckeAlg`-module structure `heckeModuleBar p`: if the geometric Hecke operators at level $p$ commute pairwise, it is the structure obtained from the ring homomorphism sending each indeterminate to the corresponding Hecke operator in $\mathrm{End}_{\mathbb{Z}}(\mathrm{JZero}\ p)$, and otherwise the structure obtained by sending every indeterminate to $0$. Let $\mathfrak{P} =$ `eisensteinMaximalIdeal p q` be the preimage, under the $\mathbb{Z}$-algebra map `eisensteinEval p` evaluating the indeterminates at the Eisenstein system of level $p$, of the ideal $(q) \subseteq \mathbb{Z}$. The assertion is that the submodule of elements of `JZero p` annihilated by every element of the set underlying $\mathfrak{P}^m$ is a finite type.
--
--   This is the finiteness of the $\mathfrak{P}^m$-torsion of the Jacobian $J_0(p)$ over $\overline{\mathbb{Q}}$ at an Eisenstein prime $\mathfrak{P}$ above $q$, in Mazur's study of the Eisenstein ideal. It supports the treatment of the Eisenstein-primary torsion as a Mazur-admissible group and the relations satisfied by elements of the $\mathfrak{P}^m$-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_torsionBySet_eisensteinMaximalIdeal_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_EisensteinIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.finite_torsionBySet_eisensteinMaximalIdeal_pow (p : ℕ) [Fact p.Prime]
    (q : ℕ) (hq : q.Prime) (m : ℕ) :
    letI := heckeModuleBar p
    Finite ↥(Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ m) : Set HeckeAlg)) := by sorry
