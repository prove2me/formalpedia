-- Prove2me | Theorems.Thm_MPECRelax_KDBConv_mpec_cpld_iff
-- name    : MPECRelax.KDBConv.mpec_cpld_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:49.903147+00:00
-- url     : https://prove2.me/theorems/ffb66ebc-7cc7-4cfa-98da-f22e0b652f88
-- title:
--   §2.2, p. 7 — MPEC-CPLD written out: positive-linear dependence of (3) at x* forces linear dependence near x*
-- statement:
--   Let $x^*$ be feasible for the MPEC (1), with index sets $I_g$, $I_{0+}$, $I_{00}$, $I_{+0}$. Then MPEC-CPLD (standard CPLD for the tightened program TNLP$(x^*)$) holds at $x^*$ if and only if the following holds: for all subsets
--   $$I_1\subseteq I_g,\quad I_2\subseteq\{1,\dots,p\},\quad I_3\subseteq I_{00}\cup I_{0+},\quad I_4\subseteq I_{00}\cup I_{+0}$$
--   such that the gradients
--   $$\{\nabla g_i(x^*)\mid i\in I_1\}\cup\big\{\{\nabla h_i(x^*)\mid i\in I_2\}\cup\{\nabla G_i(x^*)\mid i\in I_3\}\cup\{\nabla H_i(x^*)\mid i\in I_4\}\big\}\tag{3}$$
--   are positive-linearly dependent — that is, there are scalars $a_i\ge 0$ ($i\in I_1$), $b_i$ ($i\in I_2$), $c_i$ ($i\in I_3$), $d_i$ ($i\in I_4$), not all zero, with $\sum a_i\nabla g_i(x^*)+\sum b_i\nabla h_i(x^*)+\sum c_i\nabla G_i(x^*)+\sum d_i\nabla H_i(x^*)=0$ (the sign constraint applies only to the $g$-part, the vectors outside the inner brackets of (3)) — there is a neighbourhood $N(x^*)$ of $x^*$ such that the gradients
--   $$\{\nabla g_i(x)\mid i\in I_1\}\cup\{\nabla h_i(x)\mid i\in I_2\}\cup\{\nabla G_i(x)\mid i\in I_3\}\cup\{\nabla H_i(x)\mid i\in I_4\}$$
--   are linearly dependent for every $x\in N(x^*)$.
--
--   This turns the abstract Definition 2.4 into a condition stated directly in terms of the MPEC data, which is the form in which MPEC-CPLD is used in the convergence proof of Theorem 3.5.
--
--   **Formalization Note** The gradient families are indexed by the disjoint union $I_1\sqcup I_2\sqcup I_3\sqcup I_4$, so that equal gradients from different constraints count as linearly dependent. Coefficients outside the index sets are required to be zero. No differentiability hypothesis is needed: the statement is about the gradient vectors only.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 7, §2.2, display (3) and the sentence containing it

import Mathlib
import Definitions.Def_MPECRelax_KDBConv_Basic

open Filter Topology

namespace MPECRelax.KDBConv

/-- §2.2, p. 7: Definition 2.4 for CPLD written out. A feasible `xs` satisfies MPEC-CPLD
if and only if, for all `I₁ ⊆ I_g`, `I₂ ⊆ {1, …, p}`, `I₃ ⊆ I_00 ∪ I_0+`,
`I₄ ⊆ I_00 ∪ I_+0` such that the gradients (3) are positive-linearly dependent at `xs`
(sign constraint `a_i ≥ 0` only on the `g`-part, coefficients vanish off the index sets,
not all coefficients zero), the family
`{∇g_i(y) | i ∈ I₁} ∪ {∇h_i(y) | i ∈ I₂} ∪ {∇G_i(y) | i ∈ I₃} ∪ {∇H_i(y) | i ∈ I₄}`,
indexed by `I₁ ⊕ I₂ ⊕ I₃ ⊕ I₄`, is linearly dependent for all `y` in a neighbourhood
of `xs`. -/
theorem mpec_cpld_iff {n m p l : ℕ} (P : MPEC n m p l) (xs : MPECRelax.ScholtesConv.E n) (hxs : P.Feasible xs) :
    P.MPEC_CPLD xs ↔
      ∀ (I₁ : Set (Fin m)) (I₂ : Set (Fin p)) (I₃ I₄ : Set (Fin l)),
        I₁ ⊆ P.Ig xs → I₃ ⊆ P.I00 xs ∪ P.I0p xs → I₄ ⊆ P.I00 xs ∪ P.Ip0 xs →
        (∃ (a : Fin m → ℝ) (b : Fin p → ℝ) (c d : Fin l → ℝ),
          (∀ i ∈ I₁, 0 ≤ a i) ∧ (∀ i ∉ I₁, a i = 0) ∧ (∀ i ∉ I₂, b i = 0) ∧
          (∀ i ∉ I₃, c i = 0) ∧ (∀ i ∉ I₄, d i = 0) ∧
          ((∃ i, a i ≠ 0) ∨ (∃ i, b i ≠ 0) ∨ (∃ i, c i ≠ 0) ∨ (∃ i, d i ≠ 0)) ∧
          ∑ i, a i • gradient (P.g i) xs + ∑ i, b i • gradient (P.h i) xs +
            ∑ i, c i • gradient (P.G i) xs + ∑ i, d i • gradient (P.H i) xs = 0) →
        ∀ᶠ y in 𝓝 xs, ¬ LinearIndependent ℝ
          (Sum.elim (fun i : ↥I₁ => gradient (P.g i.1) y)
            (Sum.elim (fun i : ↥I₂ => gradient (P.h i.1) y)
              (Sum.elim (fun i : ↥I₃ => gradient (P.G i.1) y)
                (fun i : ↥I₄ => gradient (P.H i.1) y)))) := by sorry

end MPECRelax.KDBConv
