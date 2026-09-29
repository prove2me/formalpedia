-- Prove2me | Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus
-- name    : HeckeCharacter.IsFiniteOrderHeckeChar.exists_admitsModulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/da64bd64-8dfe-5452-a818-44bf3be5050e
-- title:
--   Finite-order Hecke characters of ℚ admit a modulus (N)
-- statement:
--   Let $\mu : (\mathbb{A}_{\mathbb{Q}})^{\times} \to \mathbb{C}^{\times}$ be a group homomorphism from the units of the adele ring of $\mathbb{Q}$ (formed over the ring of integers $\mathcal{O}_{\mathbb{Q}}$) to $\mathbb{C}^{\times}$, and assume $\mu$ satisfies the three conditions packaged in [`HeckeCharacter.IsFiniteOrderHeckeChar`](def/HeckeCharacter_FiniteOrder.html#L13): it is an idele class character, i.e. $\mu(\iota(u)) = 1$ for every $u \in \mathbb{Q}^{\times}$, where $\iota$ is induced by the structure map $\mathbb{Q} \to \mathbb{A}_{\mathbb{Q}}$; it is continuous; and it is of finite order as an element of the group of homomorphisms. The conclusion is that there is a natural number $N \neq 0$ such that $\mu$ admits the ideal $(N) =$ `Ideal.span {(N : 𝓞 ℚ)}` as a modulus in the sense of [`HeckeCharacter.AdmitsModulus`](def/HeckeCharacter_FiniteOrder.html#L21): for every idele unit $u$ whose archimedean component $u.1$ equals $1$ and whose finite component at each place $v$ of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ satisfies both $\mathrm{v}(u_v) = 1$ and $\mathrm{v}(u_v - 1) \le \exp(-m_v)$, where $m_v$ is the multiplicity `idealMultiplicity` of $v$ in the factorisation of $(N)$, one has $\mu(u) = 1$.
--
--   This is the standard statement that a finite-order Hecke character of $\mathbb{Q}$ has open kernel containing a principal congruence subgroup of the finite ideles, so that a conductor-type modulus $(N)$ exists. It is the step used by [`HeckeCharacter.IsFiniteOrderHeckeChar.exists_dirichletIdeleChar_eq`](thm.html#HeckeCharacter.IsFiniteOrderHeckeChar.exists_dirichletIdeleChar_eq), which identifies such a character with the idelic lift of a Dirichlet character modulo $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus.lean

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem HeckeCharacter.IsFiniteOrderHeckeChar.exists_admitsModulus
    {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ) :
    ∃ N : ℕ, N ≠ 0 ∧ HeckeCharacter.AdmitsModulus ℚ μ (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) := by sorry
