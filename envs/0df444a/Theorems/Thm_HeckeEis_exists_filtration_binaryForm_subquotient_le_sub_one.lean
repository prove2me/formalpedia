-- Prove2me | Theorems.Thm_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one
-- name    : HeckeEis.exists_filtration_binaryForm_subquotient_le_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/dfa7256d-0651-5bbc-93c4-21a5eea1ea3a
-- title:
--   Filtration of binary forms with Symᵃ⊗detᵇ subquotients, a≤ p-1
-- statement:
--   Let $p$ be a prime and $K$ a field of characteristic $p$, and let $n$ be a natural number. Here [`HeckeEis.BinaryForm K n`](def/HeckeEis_BinaryFormRep.html#L25) is the $K$-submodule of degree-$n$ homogeneous elements of $K[X_0,X_1]$, and [`HeckeEis.binaryFormRep K n`](def/Gamma0CoeffCohomologyEigen.html#L84) is the monoid homomorphism from the multiplicative monoid of $2\times 2$ integer matrices to the $K$-linear endomorphisms of this submodule obtained by restricting the algebra endomorphism of $K[X_0,X_1]$ that sends $X_j$ to $\sum_{i}\overline{M_{ij}}\,X_i$, i.e. the substitution $F\mapsto F(XM)$. The assertion is that there exist $r\in\mathbb N$ and a family $W_0,\dots,W_r$ of $K$-submodules of the degree-$n$ binary forms such that $W_0=\bot$, $W_r=\top$, the family is monotone, each $W_i$ is carried into itself by the substitution operator of every integer matrix $M$ with $p\nmid\det M$, and for every index $i<r$ there are natural numbers $a,b$ and a $K$-linear map $\pi$ from the degree-$n$ binary forms to the degree-$a$ binary forms with $a\le p-1$ (truncated subtraction), $\pi(W_{i+1})$ equal to the whole space of degree-$a$ forms, $W_i=W_{i+1}\cap\ker\pi$, and $\pi(M\cdot w)=(\overline{\det M})^{b}\,\bigl(M\cdot\pi(w)\bigr)$ for all integer $M$ with $p\nmid\det M$ and all $w\in W_{i+1}$.
--
--   This is the classical description of the composition factors of the symmetric powers of the standard two-dimensional representation in characteristic $p$: the successive quotients of the filtration are identified, equivariantly for all integer matrices of determinant prime to $p$, with $\mathrm{Sym}^a\otimes\det^b$ for some $0\le a\le p-1$. It is used in the passage from a Hecke eigensystem on coefficients in degree-$n$ binary forms to one with weight at most $p-1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeEis.exists_filtration_binaryForm_subquotient_le_sub_one (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (n : ℕ) :
    ∃ (r : ℕ) (W : Fin (r + 1) → Submodule K ↥(HeckeEis.BinaryForm K n)),
      W 0 = ⊥ ∧ W (Fin.last r) = ⊤ ∧ Monotone W ∧
      (∀ (i : Fin (r + 1)) (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det →
        Submodule.map (HeckeEis.binaryFormRep K n M) (W i) ≤ W i) ∧
      ∀ i : Fin r, ∃ (a b : ℕ) (π : ↥(HeckeEis.BinaryForm K n) →ₗ[K] ↥(HeckeEis.BinaryForm K a)),
        a ≤ p - 1 ∧ Submodule.map π (W i.succ) = ⊤ ∧ W i.castSucc = W i.succ ⊓ LinearMap.ker π ∧
        ∀ (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det → ∀ w ∈ W i.succ,
          π (HeckeEis.binaryFormRep K n M w)
            = (((M.det : ℤ) : K) ^ b) • HeckeEis.binaryFormRep K a M (π w) := by sorry
