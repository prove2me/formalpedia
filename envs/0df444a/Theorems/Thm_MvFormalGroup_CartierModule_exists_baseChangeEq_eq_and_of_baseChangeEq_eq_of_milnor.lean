-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor
-- name    : MvFormalGroup.CartierModule.exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/21e75322-2fc8-5e97-9c85-be070bc268ec
-- title:
--   Cartier modules are exact along a Milnor square of base rings
-- statement:
--   Fix a prime $p$ and a dimension $d$, commutative rings $B,B_0,B_1,B_{01}$ and ring homomorphisms $q_0\colon B\to B_0$, $q_1\colon B\to B_1$, $r_0\colon B_0\to B_{01}$, $r_1\colon B_1\to B_{01}$ with $r_0\circ q_0=r_1\circ q_1$, such that $(q_0,q_1)$ is jointly injective ($q_0b=0$ and $q_1b=0$ force $b=0$) and every compatible pair is in the image (for $b_0\in B_0$, $b_1\in B_1$ with $r_0b_0=r_1b_1$ there is $b\in B$ with $q_0b=b_0$, $q_1b=b_1$). Let $\Phi$ be a $d$-dimensional formal group law over $B$ ($d$ power series in $2d$ variables, with vanishing constant terms, the prescribed linear terms, and associativity), commutative in the sense that interchanging the two blocks of variables fixes each component, and let $\Phi_0,\Phi_1,\Psi$ be commutative $d$-dimensional laws over $B_0,B_1,B_{01}$ obtained by coefficientwise transport: $\Phi^{q_0}=\Phi_0$, $\Phi^{q_1}=\Phi_1$, $\Phi_0^{r_0}=\Psi=\Phi_1^{r_1}$. Here `CartierModule p Φ` consists of $d$-tuples of power series in the variables $X_0,X_1,\dots$ with zero constant term satisfying the additivity identity relating substitution of the Witt addition polynomials for $p$ into each component with substitution of the two variable-blocks into $\Phi$, and `baseChangeEq` is the additive map applying a ring homomorphism to all coefficients. The conclusion is the conjunction: base change along $q_0$ and along $q_1$ is jointly injective on `CartierModule p Φ`; and whenever $m_0$ and $m_1$ have the same image in `CartierModule p Ψ`, there is an $m$ over $B$ with base changes $m_0$ and $m_1$.
--
--   This is the exactness of the Cartier-module (curves) functor of a commutative formal group law along a Milnor square $B=B_0\times_{B_{01}}B_1$ of base rings, the typical instance being $B_0=B/J_0$, $B_1=B/J_1$, $B_{01}=B/(J_0+J_1)$ with $J_0\cap J_1=0$. It is used in the Čerednik–Drinfeld part of the development, in the analysis of special formal modules with rigidification and their quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvFormalGroup.CartierModule.exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor
    (p : ℕ) [Fact p.Prime] {d : ℕ}
    {B B₀ B₁ B₀₁ : Type} [CommRing B] [CommRing B₀] [CommRing B₁] [CommRing B₀₁]
    (q₀ : B →+* B₀) (q₁ : B →+* B₁) (r₀ : B₀ →+* B₀₁) (r₁ : B₁ →+* B₀₁)
    (hsq : r₀.comp q₀ = r₁.comp q₁)
    (hinj : ∀ b : B, q₀ b = 0 → q₁ b = 0 → b = 0)
    (hglue : ∀ (b₀ : B₀) (b₁ : B₁), r₀ b₀ = r₁ b₁ → ∃ b : B, q₀ b = b₀ ∧ q₁ b = b₁)
    (Φ : MvFormalGroup d B) [Φ.IsComm]
    (Φ₀ : MvFormalGroup d B₀) [Φ₀.IsComm] (h₀ : Φ.map q₀ = Φ₀)
    (Φ₁ : MvFormalGroup d B₁) [Φ₁.IsComm] (h₁ : Φ.map q₁ = Φ₁)
    (Ψ : MvFormalGroup d B₀₁) [Ψ.IsComm] (h₀' : Φ₀.map r₀ = Ψ) (h₁' : Φ₁.map r₁ = Ψ) :
    (∀ m : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.baseChangeEq q₀ h₀ m = 0 →
        MvFormalGroup.CartierModule.baseChangeEq q₁ h₁ m = 0 → m = 0) ∧
    (∀ (m₀ : MvFormalGroup.CartierModule p Φ₀) (m₁ : MvFormalGroup.CartierModule p Φ₁),
        MvFormalGroup.CartierModule.baseChangeEq r₀ h₀' m₀ = MvFormalGroup.CartierModule.baseChangeEq r₁ h₁' m₁ →
        ∃ m : MvFormalGroup.CartierModule p Φ,
          MvFormalGroup.CartierModule.baseChangeEq q₀ h₀ m = m₀ ∧
          MvFormalGroup.CartierModule.baseChangeEq q₁ h₁ m = m₁) := by sorry
