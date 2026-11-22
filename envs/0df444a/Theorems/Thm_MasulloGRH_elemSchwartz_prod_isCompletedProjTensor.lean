-- Prove2me | Theorems.Thm_MasulloGRH_elemSchwartz_prod_isCompletedProjTensor
-- name    : MasulloGRH.elemSchwartz_prod_isCompletedProjTensor
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:01:42.61712+00:00
-- url     : https://prove2.me/theorems/a75456a2-67e6-47bf-bd56-9b4992e2abda
-- title:
--   Kernel theorem for elementary abelian Lie groups: $\mathcal S(A_1)\,\widehat\otimes_\pi\,\mathcal S(A_2)\cong\mathcal S(A_1\times A_2)$
-- statement:
--   **Kernel theorem for elementary abelian Lie groups** (auxiliary lemma for the proof of Lemma D.1.8.1(1)): $\mathcal S(A_1)\,\widehat\otimes_\pi\,\mathcal S(A_2)\cong\mathcal S(A_1\times A_2)$.
--
--   For $i=1,2$ let
--   $$A_i=\mathbb R^{m_i}\times\mathbb T^{n_i}\times\mathbb Z^{r_i}\times\prod_{l<s_i}\mathbb Z/d_{i,l}\mathbb Z\qquad(\mathbb T=\mathbb R/\mathbb Z,\ d_{i,l}\neq 0)$$
--   be elementary abelian Lie groups, and let $\mathcal S(A_i)$ be their Schwartz–Bruhat spaces (Definition D.1.3.1): the functions on $A_i$ that are smooth in the variables of $\mathbb R^{m_i}\times\mathbb T^{n_i}$ and of rapid decay, with the topology of the seminorms $\sup|a|^j|x|^i\,\|D^kg(x,z,a,b)\|$.
--
--   **Statement.** There are an elementary abelian Lie group $A=\mathbb R^{m}\times\mathbb T^{n}\times\mathbb Z^{r}\times\prod_{l<s}\mathbb Z/d_l\mathbb Z$ (with all $d_l\neq0$), an isomorphism of topological groups $\varphi\colon A_1\times A_2\to A$ and a linear map $j\colon\mathcal S(A_1)\otimes\mathcal S(A_2)\to\mathcal S(A)$ on the algebraic tensor product such that
--   $$j(f\otimes g)\bigl(\varphi(x,y)\bigr)=f(x)\,g(y)\qquad(f\in\mathcal S(A_1),\ g\in\mathcal S(A_2),\ x\in A_1,\ y\in A_2),$$
--   and $(\mathcal S(A),j)$ is a completed projective tensor product $\mathcal S(A_1)\,\widehat\otimes_\pi\,\mathcal S(A_2)$: $\mathcal S(A)$ is a complete Hausdorff locally convex space, $j$ is injective with dense range, and the projective tensor topology of $\mathcal S(A_1)\otimes_\pi\mathcal S(A_2)$ is the topology induced by $j$.
--
--   Here one may take $m=m_1+m_2$, $n=n_1+n_2$, $r=r_1+r_2$, $s=s_1+s_2$, $(d_l)$ the concatenation of $(d_{1,l})$ and $(d_{2,l})$, and $\varphi$ the regrouping of coordinates; then $\mathcal S(A)=\mathcal S(A_1\times A_2)$.
--
--   This is the elementary case of the kernel theorem for Schwartz–Bruhat spaces; for $A_i=\mathbb R^{m_i}$ it is the Schwartz kernel theorem $\mathcal S(\mathbb R^{m_1})\,\widehat\otimes_\pi\,\mathcal S(\mathbb R^{m_2})\cong\mathcal S(\mathbb R^{m_1+m_2})$ (§C.2.2.3, §C.2.4.6). In the proof of Lemma D.1.8.1(1) it is applied to the quotients $\Gamma_i/k_i$ of structural pairs, giving the stage-by-stage form $\mathcal S(k_1,\Gamma_1)\,\widehat\otimes_\pi\,\mathcal S(k_2,\Gamma_2)\cong\mathcal S(k_1\times k_2,\Gamma_1\times\Gamma_2)$ of the kernel theorem $\mathcal S(G_1)\,\overline\otimes\,\mathcal S(G_2)\cong\mathcal S(G_1\times G_2)$.
--
--   **Formalization Note.** The groups and spaces are `ElemGroup` and `ElemSchwartz` of the platform definition `MasulloGRH_SchwartzBruhat`, the completed tensor product is the predicate `IsCompletedProjTensor` of `TopologicalTensorProduct_Completion`, and $\varphi$ is a `ContinuousAddEquiv` (`≃ₜ+`). The group $A$ and the isomorphism $\varphi$ are existentially quantified, so that the regrouping of coordinates (with its dependent `ZMod` factors) need not be written out in the statement; $j(f\otimes g)$ is described through its underlying function `ElemSchwartz.toFun`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 778, Lemma D.1.8.1(1); auxiliary lemma for the proof of Lemma D.1.8.1(1) (child of MasulloGRH.schwartzBruhat_prod_stages_isCompletedProjTensor): kernel theorem for the Schwartz–Bruhat spaces of elementary abelian Lie groups (Definition D.1.3.1, p. 750)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_TopologicalTensorProduct_Completion

open TensorProduct

set_option autoImplicit false

namespace MasulloGRH

theorem elemSchwartz_prod_isCompletedProjTensor
    (m₁ n₁ r₁ s₁ : ℕ) (d₁ : Fin s₁ → ℕ) (m₂ n₂ r₂ s₂ : ℕ) (d₂ : Fin s₂ → ℕ)
    (hd₁ : ∀ i, d₁ i ≠ 0) (hd₂ : ∀ i, d₂ i ≠ 0) :
    ∃ (m n r s : ℕ) (d : Fin s → ℕ)
      (φ : (ElemGroup m₁ n₁ r₁ s₁ d₁ × ElemGroup m₂ n₂ r₂ s₂ d₂) ≃ₜ+ ElemGroup m n r s d)
      (j : ElemSchwartz m₁ n₁ r₁ s₁ d₁ ⊗[ℂ] ElemSchwartz m₂ n₂ r₂ s₂ d₂ →ₗ[ℂ]
        ElemSchwartz m n r s d),
      (∀ i, d i ≠ 0) ∧
      (∀ (f : ElemSchwartz m₁ n₁ r₁ s₁ d₁) (g : ElemSchwartz m₂ n₂ r₂ s₂ d₂)
          (x : ElemGroup m₁ n₁ r₁ s₁ d₁) (y : ElemGroup m₂ n₂ r₂ s₂ d₂),
          (j (f ⊗ₜ[ℂ] g)).toFun (φ (x, y)) = f.toFun x * g.toFun y) ∧
      IsCompletedProjTensor (ElemSchwartz m₁ n₁ r₁ s₁ d₁) (ElemSchwartz m₂ n₂ r₂ s₂ d₂) j := by
  sorry

end MasulloGRH
