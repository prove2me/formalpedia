-- Prove2me | Theorems.Thm_Module_Basis_exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul
-- name    : Module.Basis.exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/7dad7c84-de75-5f1a-b86c-5acd6d183eee
-- title:
--   Lifting a mod p common eigenvector to a p-primitive lattice vector
-- statement:
--   Let $\Lambda$ be an additive commutative group equipped with a $\mathbb{Z}$-basis $b$ indexed by $\mathrm{Fin}\,t$ for some natural number $t$, let $I$ be an index type, let $T : I \to \Lambda \to_{\mathbb{Z}} \Lambda$ be a family of $\mathbb{Z}$-linear endomorphisms of $\Lambda$ and $n : I \to \mathbb{Z}$ a family of integers. Let $p$ be a prime and $\kappa$ a field of characteristic $p$. Suppose given a vector $m : \mathrm{Fin}\,t \to \kappa$ with $m \neq 0$ such that for every $i \in I$ the matrix of $T i$ in the basis $b$, with entries mapped into $\kappa$ by the integer cast, satisfies $\overline{M_i}\, m = (n_i \bmod p)\, m$, i.e. its product (as `Matrix.mulVec`) with $m$ equals the scalar $n_i$, cast into $\kappa$, times $m$. The conclusion asserts the existence of $v \in \Lambda$ such that $v$ is not of the form $p \cdot w$ for any $w \in \Lambda$, and such that for every $i \in I$ there is $w \in \Lambda$ with $T_i v - n_i v = p \cdot w$; that is, $v \notin p\Lambda$ while $T_i v \equiv n_i v \pmod{p\Lambda}$ for all $i$.
--
--   This is the integral lifting step which turns a common eigenvector, over an arbitrary field of characteristic $p$, of the reductions of a family of integral operators into a vector of the lattice itself that is primitive modulo $p$ and satisfies the eigenvalue congruences. It is applied to the parabolic integral cohomology lattice with the Hecke and diamond operators, via [`CohCarrier.exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul`](thm.html#CohCarrier.exists_H1_int_mem_parabolicHoms_not_exists_eq_smul_of_mem_parabolicHoms_of_diamondRaw_eq_of_heckeT_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Basis_exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.Basis.exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul
    {Λ : Type*} [AddCommGroup Λ] {t : ℕ} (b : Module.Basis (Fin t) ℤ Λ)
    {I : Type*} (T : I → Λ →ₗ[ℤ] Λ) (n : I → ℤ)
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p]
    (m : Fin t → κ) (hm : m ≠ 0)
    (heig : ∀ i, ((LinearMap.toMatrix b b (T i)).map (Int.cast : ℤ → κ)).mulVec m = (n i : κ) • m) :
    ∃ v : Λ, (¬ ∃ w : Λ, v = (p : ℤ) • w) ∧ ∀ i, ∃ w : Λ, T i v - n i • v = (p : ℤ) • w := by sorry
