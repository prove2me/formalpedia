-- Prove2me | Theorems.Thm_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top
-- name    : LinearMap.exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/36b21926-6259-5c89-8a13-d69b9ad28986
-- title:
--   Two presentations give Jⁿ⁺¹-congruent classes after a uniform shift
-- statement:
--   Let $B$ be a commutative Noetherian ring, $J \subseteq B$ an ideal, $G_E$ a $B$-module and $G_K$ a finite $B$-module. Let $(F_k)_{k \in \mathbb{N}}$, $(E_k)_{k \in \mathbb{N}}$ be families of $B$-modules together with $B$-linear maps $\varepsilon_k \colon F_k \to E_k$, $\psi^E_k \colon G_E \to E_k$ and $\lambda_k \colon G_K \to F_k$ such that $\operatorname{range}\lambda_k = \ker\varepsilon_k$ for every $k$, and such that for some $c_0$ one has $\ker \lambda_{k+c_0} \subseteq J^{k+1} \cdot G_K$ for all $k$. Let $p_1 \colon B^{r_1} \to G_E$ and $p_2 \colon B^{r_2} \to G_E$ be surjective $B$-linear maps and let $P \colon B^{r_1+r_2} \to G_E$ satisfy $P(\mathrm{append}(v,w)) = p_1 v + p_2 w$. Then there is $c \in \mathbb{N}$ with the following property. For every $n$, writing $m = n + c$, given $B$-linear $\ell_a \colon B^{r_a} \to F_m$ with $\varepsilon_m \circ \ell_a = \psi^E_m \circ p_a$ and $B$-linear $\delta_a \colon \ker p_a \to G_K$ with $\lambda_m \circ \delta_a = \ell_a$ restricted to $\ker p_a$, for $a = 1, 2$, there exist $B$-linear $\delta_1', \delta_2' \colon \ker P \to G_K$ such that $\delta_1'(\mathrm{append}(s,0)) = \delta_1(s)$ for every $s \in \ker p_1$, $\delta_2'(\mathrm{append}(0,s)) = \delta_2(s)$ for every $s \in \ker p_2$ (in both cases for any proof that the appended vector lies in $\ker P$), and such that the classes of $\delta_1'$ and $\delta_2'$ in the quotient of $\operatorname{Hom}_B(\ker P, G_K)$ by the submodule of restrictions to $\ker P$ of homomorphisms $B^{r_1+r_2} \to G_K$ differ by an element of $J^{n+1} \cdot \top$.
--
--   This is the comparison, on a single overlap, of the classes obtained from two finite presentations of the same module: after a shift $c$ depending only on $B$, $J$ and the modules involved, the two classes agree modulo $J^{n+1}$, the shift being produced by an Artin–Rees type uniformity for homomorphism modules ([`LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul`](thm.html#LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul)). It is used in the construction of formal splitting data along an ordered affine cover for a proper morphism over an adically complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type v} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    (F E : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (ε : ∀ k, F k →ₗ[B] E k) (ψE : ∀ k, GE →ₗ[B] E k) (lam : ∀ k, GK →ₗ[B] F k)
    (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (hlami : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (lam (k + c)) ≤ J ^ (k + 1) • (⊤ : Submodule B GK))
    {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] GE) (hp₁ : Function.Surjective p₁)
    (p₂ : (Fin r₂ → B) →ₗ[B] GE) (hp₂ : Function.Surjective p₂)
    (P : (Fin (r₁ + r₂) → B) →ₗ[B] GE) (hP : ∀ (v : Fin r₁ → B) (w : Fin r₂ → B), P (Fin.append v w) = p₁ v + p₂ w) :
    ∃ c : ℕ, ∀ (n : ℕ)
      (ℓ₁ : (Fin r₁ → B) →ₗ[B] F (n + c)) (_ : ε (n + c) ∘ₗ ℓ₁ = ψE (n + c) ∘ₗ p₁)
      (ℓ₂ : (Fin r₂ → B) →ₗ[B] F (n + c)) (_ : ε (n + c) ∘ₗ ℓ₂ = ψE (n + c) ∘ₗ p₂)
      (δ₁ : ↥(LinearMap.ker p₁) →ₗ[B] GK) (_ : lam (n + c) ∘ₗ δ₁ = ℓ₁ ∘ₗ (LinearMap.ker p₁).subtype)
      (δ₂ : ↥(LinearMap.ker p₂) →ₗ[B] GK) (_ : lam (n + c) ∘ₗ δ₂ = ℓ₂ ∘ₗ (LinearMap.ker p₂).subtype),
      ∃ δ₁' δ₂' : ↥(LinearMap.ker P) →ₗ[B] GK,
        (∀ (s : ↥(LinearMap.ker p₁)) (hs : Fin.append (s : Fin r₁ → B) (0 : Fin r₂ → B) ∈ LinearMap.ker P),
          δ₁' ⟨Fin.append (s : Fin r₁ → B) 0, hs⟩ = δ₁ s) ∧
        (∀ (s : ↥(LinearMap.ker p₂)) (hs : Fin.append (0 : Fin r₁ → B) (s : Fin r₂ → B) ∈ LinearMap.ker P),
          δ₂' ⟨Fin.append 0 (s : Fin r₂ → B), hs⟩ = δ₂ s) ∧
        Submodule.Quotient.mk δ₁' - Submodule.Quotient.mk δ₂' ∈
          J ^ (n + 1) • (⊤ : Submodule B ((↥(LinearMap.ker P) →ₗ[B] GK) ⧸
            LinearMap.range (LinearMap.lcomp B GK (LinearMap.ker P).subtype))) := by sorry
