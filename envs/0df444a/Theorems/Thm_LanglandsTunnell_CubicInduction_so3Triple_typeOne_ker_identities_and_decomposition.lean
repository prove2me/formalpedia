-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition
-- name    : LanglandsTunnell.CubicInduction.so3Triple_typeOne_ker_identities_and_decomposition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/25dd1aa4-fc3c-5b5e-9091-9b5df5781179
-- title:
--   Type-one mathfrakso₃-triples: kernel identities and splitting
-- statement:
--   Let $V$ be a complex vector space and $F \subseteq V$ a finite-dimensional subspace, and let $J_1, J_2, J_3$ be $\mathbb{C}$-linear endomorphisms of $V$ each of which maps $F$ into $F$. Assume that on $F$ the three commutator relations $J_1 J_2 f - J_2 J_1 f = J_3 f$, $J_2 J_3 f - J_3 J_2 f = J_1 f$ and $J_3 J_1 f - J_1 J_3 f = J_2 f$ hold for all $f \in F$, together with the Casimir relation $J_1^2 f + J_2^2 f + J_3^2 f = -2f$ on $F$. Assume further given a function $B : V \times V \to \mathbb{C}$ which, restricted to $F$, is linear in its first argument (i.e. $B(zw_1 + w_2, w') = z\,B(w_1,w') + B(w_2,w')$ for $z \in \mathbb{C}$ and $w_1, w_2, w' \in F$), Hermitian-symmetric ($B(w',w) = \overline{B(w,w')}$ for $w, w' \in F$), positive in the sense that $\operatorname{Re} B(w,w) > 0$ for every nonzero $w \in F$, and for which each $J_i$ is skew: $B(J_i x, y) = -B(x, J_i y)$ for $x, y \in F$ and $i = 1,2,3$. The conclusion is twofold. First, every $h \in F$ with $J_3 h = 0$ satisfies $J_1^2 h = -h$, $J_2^2 h = -h$, $J_1 J_2 h = 0$ and $J_2 J_1 h = 0$. Second, for every $x \in F$ the three vectors $J_2 J_3^2 x$, $J_1 J_3^2 x$ and $x + J_3^2 x$ are annihilated by $J_3$, and $$x = J_2\bigl(J_2 J_3^2 x\bigr) + J_1\bigl(J_1 J_3^2 x\bigr) + \bigl(x + J_3^2 x\bigr).$$
--
--   This is the elementary structure theory of a finite-dimensional unitary $\mathfrak{so}_3$-module on which the Casimir element acts by $-2$, that is, one all of whose irreducible constituents are the standard three-dimensional representation: the kernel of $J_3$ carries the whole module, each vector being recovered from its $J_3$-kernel components by applying $J_1$ and $J_2$. It is used in the cubic-induction part of the Langlands–Tunnell input, by [`LanglandsTunnell.CubicInduction.mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero`](thm.html#LanglandsTunnell.CubicInduction.mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.so3Triple_typeOne_ker_identities_and_decomposition
    {V : Type*} [AddCommGroup V] [Module ℂ V] (F : Submodule ℂ V) [FiniteDimensional ℂ F] (J₁ J₂ J₃ : Module.End ℂ V)
    (hF₁ : ∀ f ∈ F, J₁ f ∈ F) (hF₂ : ∀ f ∈ F, J₂ f ∈ F) (hF₃ : ∀ f ∈ F, J₃ f ∈ F)
    (h12 : ∀ f ∈ F, J₁ (J₂ f) - J₂ (J₁ f) = J₃ f)
    (h23 : ∀ f ∈ F, J₂ (J₃ f) - J₃ (J₂ f) = J₁ f)
    (h31 : ∀ f ∈ F, J₃ (J₁ f) - J₁ (J₃ f) = J₂ f)
    (hcas : ∀ f ∈ F, J₁ (J₁ f) + J₂ (J₂ f) + J₃ (J₃ f) = (-2 : ℂ) • f)
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ F, ∀ w₂ ∈ F, ∀ w' ∈ F, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ F, ∀ w' ∈ F, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ F, w ≠ 0 → 0 < (B w w).re)
    (hskew₁ : ∀ x ∈ F, ∀ y ∈ F, B (J₁ x) y = -B x (J₁ y))
    (hskew₂ : ∀ x ∈ F, ∀ y ∈ F, B (J₂ x) y = -B x (J₂ y))
    (hskew₃ : ∀ x ∈ F, ∀ y ∈ F, B (J₃ x) y = -B x (J₃ y)) :
    (∀ h ∈ F, J₃ h = 0 → J₁ (J₁ h) = -h ∧ J₂ (J₂ h) = -h ∧ J₁ (J₂ h) = 0 ∧ J₂ (J₁ h) = 0) ∧
    (∀ x ∈ F, J₃ (J₂ (J₃ (J₃ x))) = 0 ∧ J₃ (J₁ (J₃ (J₃ x))) = 0 ∧ J₃ (x + J₃ (J₃ x)) = 0 ∧
      x = J₂ (J₂ (J₃ (J₃ x))) + J₁ (J₁ (J₃ (J₃ x))) + (x + J₃ (J₃ x))) := by sorry
