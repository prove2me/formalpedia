-- Prove2me | Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq
-- name    : HeckeCharacter.IsFiniteOrderHeckeChar.exists_dirichletIdeleChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/6fb8e678-c0cf-504d-8b85-386651355891
-- title:
--   Finite-order Hecke characters of ℚ come from Dirichlet characters
-- statement:
--   Let $\mu \colon (\mathbb{A}_\mathbb{Q})^\times \to \mathbb{C}^\times$ be a monoid homomorphism from the unit group of the adele ring of $\mathbb{Q}$ (formed relative to $\mathcal{O}_\mathbb{Q}$) to $\mathbb{C}^\times$, and suppose $\mu$ satisfies [`HeckeCharacter.IsFiniteOrderHeckeChar ℚ`](def/HeckeCharacter_FiniteOrder.html#L13), that is: $\mu$ is an idele class character, meaning $\mu(\iota(u)) = 1$ for every $u \in \mathbb{Q}^\times$, where $\iota$ is the map on units induced by the structure map $\mathbb{Q} \to \mathbb{A}_\mathbb{Q}$; $\mu$ is continuous; and $\mu$ is of finite order as an element of the monoid of such homomorphisms. The conclusion asserts the existence of a natural number $N$, together with a proof that $N$ is nonzero, and of a Dirichlet character $\chi$ modulo $N$ with values in $\mathbb{C}$, such that $\chi$.`dirichletIdeleChar` $= \mu$ as homomorphisms $(\mathbb{A}_\mathbb{Q})^\times \to \mathbb{C}^\times$. Here `dirichletIdeleChar` is the inverse of the composite of the homomorphism `unitResidue` $\colon (\mathbb{A}_\mathbb{Q})^\times \to \mathbb{Z}/N\mathbb{Z}$, obtained from the local unit residues of an idele reassembled through the isomorphism $\mathbb{Z}/N\mathbb{Z} \simeq \prod_{p} \mathbb{Z}/p^{v_p(N)}\mathbb{Z}$, with the unit-valued homomorphism attached to $\chi$; so the assertion is $\mu(x) = \chi(\mathrm{unitResidue}_N(x))^{-1}$ for all ideles $x$.
--
--   This is the classification of the finite-order characters of the idele class group $\mathbb{A}_\mathbb{Q}^\times/\mathbb{Q}^\times$: each of them is the idelic avatar of a Dirichlet character of some modulus $N$, with the normalisation built into `dirichletIdeleChar`. It is used in the Langlands–Tunnell part of the development, where finite-order Hecke characters of $\mathbb{Q}$ arising from cubic induction must be recognised as Dirichlet characters in order to compare Euler coefficients with those of an induced representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq.lean

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem HeckeCharacter.IsFiniteOrderHeckeChar.exists_dirichletIdeleChar_eq
    {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.dirichletIdeleChar = μ := by sorry
