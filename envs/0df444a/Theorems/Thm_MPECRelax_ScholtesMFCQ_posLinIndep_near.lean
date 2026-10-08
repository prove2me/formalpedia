-- Prove2me | Theorems.Thm_MPECRelax_ScholtesMFCQ_posLinIndep_near
-- name    : MPECRelax.ScholtesMFCQ.posLinIndep_near
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:52.443258+00:00
-- url     : https://prove2.me/theorems/3aa390ae-67db-4a58-b844-b91b65ecbe22
-- title:
--   Proof of Theorem 3.2, pp. 11–12 — positive-linear independence persists near x*
-- statement:
--   Let the data $f,g,h,G,H$ of the MPEC (1) be continuously differentiable, let $x^*$ be feasible for (1), and let MPEC-MFCQ hold at $x^*$. With the index sets $I_g, I_{00}, I_{0+}, I_{+0}$ taken at $x^*$, the family
--   $$\{\nabla g_i(x)\mid i\in I_g\}\cup\big\{\{\nabla h_i(x)\mid i=1,\dots,p\}\cup\{\nabla G_i(x)\mid i\in I_{00}\cup I_{0+}\}\cup\{\nabla H_i(x)\mid i\in I_{00}\cup I_{+0}\}\big\}$$
--   (sign constraint on the $\nabla g_i$ only) is positive-linearly independent for all $x\in X^S(t)$ sufficiently close to $x^*$, where $X^S(t)$ is the feasible set of Scholtes' relaxed program $R^S(t)$, $t>0$.
--
--   The paper states this "for all $x\in X^S(t)$ sufficiently close to $x^*$", citing Qi and Wei [29, Prop. 2.2], with $t$ fixed by the context; we state it with one neighbourhood $N$ of $x^*$ that serves every $t>0$, as the theorem's proof requires.
--
--   **Formalization Note.** "For all $x\in X^S(t)$ sufficiently close to $x^*$" is: there is $N\in\mathcal N(x^*)$ (`N ∈ 𝓝 xs`) such that for all $t>0$ and all $x\in N$ feasible for $R^S(t)$. Positive-linear independence is written out explicitly: a vanishing combination with $\lambda\ge0$ supported in $I_g$, $\gamma$ supported in $I_{00}\cup I_{0+}$ and $\nu$ supported in $I_{00}\cup I_{+0}$ has all coefficients zero. The C¹ standing assumption of p. 1 is the hypothesis `IsC1`.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 11–12, proof of Theorem 3.2

import Mathlib
import Definitions.Def_MPECRelax_ScholtesMFCQ_Basic

open Filter Topology
open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesMFCQ

/-- Proof of Theorem 3.2 (pp. 11–12): under the C¹ standing assumption and MPEC-MFCQ at a
feasible `xs`, there is a neighbourhood `N` of `xs`, the same for every `t > 0`, such that
for every `x ∈ N ∩ X^S(t)` the family of the previous step, with the index sets of `xs` but
the gradients evaluated at `x`, is positive-linearly independent. -/
theorem posLinIndep_near {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1) (xs : MPECRelax.ScholtesConv.E n)
    (hfeas : P.Feasible xs) (hCQ : P.MPEC_MFCQ xs) :
    ∃ N ∈ 𝓝 xs, ∀ t : ℝ, 0 < t → ∀ x ∈ N, (P.RS t).Feasible x →
      ∀ (lam : Fin m → ℝ) (mu : Fin p → ℝ) (γ ν : Fin l → ℝ),
        (∀ i, 0 ≤ lam i) → (∀ i ∉ P.Ig xs, lam i = 0) →
        (∀ i ∉ P.I00 xs ∪ P.I0p xs, γ i = 0) → (∀ i ∉ P.I00 xs ∪ P.Ip0 xs, ν i = 0) →
        ∑ i, lam i • gradient (P.g i) x + ∑ i, mu i • gradient (P.h i) x +
            ∑ i, γ i • gradient (P.G i) x + ∑ i, ν i • gradient (P.H i) x = 0 →
        lam = 0 ∧ mu = 0 ∧ γ = 0 ∧ ν = 0 := by sorry

end MPECRelax.ScholtesMFCQ
