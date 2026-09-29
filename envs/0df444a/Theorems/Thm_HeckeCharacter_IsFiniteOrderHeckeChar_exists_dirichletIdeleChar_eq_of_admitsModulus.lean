-- Prove2me | Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq_of_admitsModulus
-- name    : HeckeCharacter.IsFiniteOrderHeckeChar.exists_dirichletIdeleChar_eq_of_admitsModulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/6c1e6615-0120-5455-a7c9-ba082610d72c
-- title:
--   Finite-order Hecke characters of ℚ of modulus (N) are Dirichlet
-- statement:
--   Let $\mu \colon (\mathbb{A}_\mathbb{Q})^\times \to \mathbb{C}^\times$ be a group homomorphism on the units of the adele ring of $\mathbb{Q}$ (over $\mathcal{O}_\mathbb{Q}$) which is a finite-order Hecke character of $\mathbb{Q}$, that is: $\mu$ kills the principal ideles, $\mu(\iota(u)) = 1$ for all $u \in \mathbb{Q}^\times$ with $\iota$ induced by $\mathbb{Q} \to \mathbb{A}_\mathbb{Q}$; $\mu$ is continuous; and $\mu$ is of finite order. Let $N$ be a nonzero natural number, and assume $\mu$ admits the modulus given by the ideal $(N) =$ `Ideal.span {(N : 𝓞 ℚ)}`, i.e. $\mu(u) = 1$ for every adelic unit $u$ whose infinite component is $1$ and whose finite-adelic component satisfies, at every height-one prime $v$ of $\mathcal{O}_\mathbb{Q}$, both $\mathrm{v}(u_v) = 1$ and $\mathrm{v}(u_v - 1) \le \exp(-m_v)$, where $m_v$ is the number of times $v$ occurs in the factorisation of $(N)$. The conclusion is that there exists a Dirichlet character $\chi$ modulo $N$ with values in $\mathbb{C}$ such that the character $x \mapsto \chi(\bar{u}_N(x))^{-1}$ attached to $\chi$ — the inverse of the composite of the unit-residue homomorphism $\bar{u}_N \colon (\mathbb{A}_\mathbb{Q})^\times \to \mathbb{Z}/N\mathbb{Z}$ with $\chi$ — equals $\mu$ as a homomorphism $(\mathbb{A}_\mathbb{Q})^\times \to \mathbb{C}^\times$.
--
--   This is one half of the classical dictionary between finite-order idele class characters of $\mathbb{Q}$ and Dirichlet characters, stated at a fixed modulus: every finite-order Hecke character admitting the modulus $(N)$ comes from a Dirichlet character mod $N$. It feeds the unconditional classification of finite-order Hecke characters of $\mathbb{Q}$ and, through it, the identification of nebentypus characters of normalised eigenforms occurring in the modular-curve cohomology used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq_of_admitsModulus.lean

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem HeckeCharacter.IsFiniteOrderHeckeChar.exists_dirichletIdeleChar_eq_of_admitsModulus
    {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ)
    {N : ℕ} [NeZero N] (hmod : HeckeCharacter.AdmitsModulus ℚ μ (Ideal.span {((N : ℕ) : 𝓞 ℚ)})) :
    ∃ χ : DirichletCharacter ℂ N, χ.dirichletIdeleChar = μ := by sorry
