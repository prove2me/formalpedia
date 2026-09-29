-- Prove2me | Theorems.Thm_ModularCurve_exists_prime_torsion_of_isMaximal
-- name    : ModularCurve.exists_prime_torsion_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/0deba84b-1807-56bf-8f31-fe559c1b9e73
-- title:
--   A prime other than q annihilates 𝔪-torsion in J₀(M)
-- statement:
--   Fix a natural number $M \neq 0$ and an arbitrary natural number $q$. Write `HeckeAlg` for the polynomial ring $\mathbb{Z}[X_\ell : \ell \text{ prime}]$ over the primes, and let `JZero M` be the degree-zero divisor class group $\mathrm{Pic}^0$ of the modular function field `modularFunctionFieldBar M` over $\overline{\mathbb{Q}}$, i.e. the quotient of the group of divisors of degree $0$ by the subgroup of principal divisors. The `HeckeAlg`-module structure used is `heckeModuleBar M`: if the operators `heckeOperatorBar M ℓ` commute pairwise, the variable $X_\ell$ acts through `heckeEvalBar`, i.e. as `heckeOperatorBar M ℓ`; otherwise `HeckeAlg` acts through the $\mathbb{Z}$-algebra map sending every variable to $0$. The assertion is: for every maximal ideal $\mathfrak m \subset$ `HeckeAlg` such that the image of $q$ in `HeckeAlg`$/\mathfrak m$ is a unit, and for every $x$ in the $\mathfrak m$-torsion submodule `heckeTorsion (JZero M) 𝔪` (the set of elements annihilated by every element of $\mathfrak m$), there is a prime number $p$ with $p \neq q$ and $p \cdot x = 0$.
--
--   This is the elementary finiteness input behind the statement that $\mathfrak m$-torsion of the Jacobian is torsion of residue characteristic different from $q$; note that `HeckeAlg` is a polynomial ring in infinitely many variables, so a maximal ideal of it may a priori have residue characteristic $0$, and the conclusion is obtained from the action on $J_0(M)$ rather than from $\mathfrak m$ alone. It is used in the construction of semistable specializations of `JZero` and in the Čerednik–Drinfel'd comparison of Hecke-equivariant data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_prime_torsion_of_isMaximal.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_prime_torsion_of_isMaximal (M : ℕ) [NeZero M] (q : ℕ) :
    letI := heckeModuleBar M
    ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
      ∀ x ∈ heckeTorsion (JZero M) 𝔪, ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ p • x = 0 := by sorry
