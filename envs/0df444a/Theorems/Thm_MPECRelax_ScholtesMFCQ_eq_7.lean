-- Prove2me | Theorems.Thm_MPECRelax_ScholtesMFCQ_eq_7
-- name    : MPECRelax.ScholtesMFCQ.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:06.48087+00:00
-- url     : https://prove2.me/theorems/e7c86b8c-baa6-4126-87d5-9fec5a432397
-- title:
--   (7) — the active gradients of R^S(t) are positive-linearly independent near x*
-- statement:
--   Let the data of the MPEC (1) be continuously differentiable, let $x^*$ be feasible for (1), and let MPEC-MFCQ hold at $x^*$. Then there is a neighbourhood $N(x^*)$, independent of $t$, such that for every $t>0$ and every $x\in X^S(t)\cap N(x^*)$ the family of vectors
--   $$\begin{array}{ll}
--   \nabla g_i(x) & (i\in I_g(x)),\\
--   \nabla h_i(x) & (i=1,\dots,p),\\
--   \nabla G_i(x) & (i\in I_G(x)),\\
--   \nabla H_i(x) & (i\in I_H(x)),\\
--   G_i(x)\nabla H_i(x)+H_i(x)\nabla G_i(x) & (i\in I_{GH}(x;t)\cap I_{0+}),\\
--   G_i(x)\nabla H_i(x)+H_i(x)\nabla G_i(x) & (i\in I_{GH}(x;t)\cap I_{+0}),\\
--   \nabla G_i(x) & (i\in I_{GH}(x;t)\cap I_{00}),\\
--   \nabla H_i(x) & (i\in I_{GH}(x;t)\cap I_{00})
--   \end{array}$$
--   is positive-linearly independent, with the sign constraint on the coefficients of the $\nabla g_i(x)$ only: a vanishing combination with nonnegative coefficients on the first line and arbitrary coefficients on the other seven lines has all coefficients zero.
--
--   This is the last ingredient of the proof of Theorem 3.2: the multiplier equation of MFCQ for $R^S(t)$ (via Remark 2.2) is a combination of these vectors.
--
--   **Formalization Note.** Two readings are fixed. (a) The sixth line is printed as $G_i(x)\nabla H_i(x)+G_i(x)\nabla H_i(x)$, a misprint for the gradient $G_i(x)\nabla H_i(x)+H_i(x)\nabla G_i(x)$ of $G_iH_i$ (as in (8)); the corrected vector is used. (b) The paper does not mark which vectors of (7) carry a sign constraint; it inherits the bracket convention of the preceding display, where only the $\nabla g_i$ are sign-constrained, and this is the only reading under which (7) applies to (9), where the $\nabla G_i$, $\nabla H_i$ coefficients are nonpositive. Each line has its own coefficient vector, supported in its index set; $I_{0+}, I_{+0}, I_{00}$ are taken at $x^*$.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 12, proof of Theorem 3.2, (7)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesMFCQ_Basic

open Filter Topology
open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesMFCQ

/-- (7), proof of Theorem 3.2 (p. 12): under the C¹ standing assumption and MPEC-MFCQ at
a feasible `xs`, there is a neighbourhood `N` of `xs`, the same for every `t > 0`,
such that for every `x ∈ N ∩ X^S(t)` the family
`∇g_i(x)` (`i ∈ I_g(x)`), `∇h_i(x)` (all `i`), `∇G_i(x)` (`i ∈ I_G(x)`),
`∇H_i(x)` (`i ∈ I_H(x)`), `G_i(x)∇H_i(x) + H_i(x)∇G_i(x)` (`i ∈ I_GH(x;t) ∩ I_0+`),
`G_i(x)∇H_i(x) + H_i(x)∇G_i(x)` (`i ∈ I_GH(x;t) ∩ I_+0`), `∇G_i(x)`
(`i ∈ I_GH(x;t) ∩ I_00`), `∇H_i(x)` (`i ∈ I_GH(x;t) ∩ I_00`)
is positive-linearly independent, the sign constraint being on the `∇g_i` only. -/
theorem eq_7 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1) (xs : MPECRelax.ScholtesConv.E n)
    (hfeas : P.Feasible xs) (hCQ : P.MPEC_MFCQ xs) :
    ∃ N ∈ 𝓝 xs, ∀ t : ℝ, 0 < t → ∀ x ∈ N, (P.RS t).Feasible x →
      ∀ (lam : Fin m → ℝ) (mu : Fin p → ℝ) (a b c₁ c₂ d e : Fin l → ℝ),
        (∀ i, 0 ≤ lam i) → (∀ i ∉ P.Ig x, lam i = 0) →
        (∀ i ∉ P.IG x, a i = 0) → (∀ i ∉ P.IH x, b i = 0) →
        (∀ i ∉ P.IGH x t ∩ P.I0p xs, c₁ i = 0) → (∀ i ∉ P.IGH x t ∩ P.Ip0 xs, c₂ i = 0) →
        (∀ i ∉ P.IGH x t ∩ P.I00 xs, d i = 0) → (∀ i ∉ P.IGH x t ∩ P.I00 xs, e i = 0) →
        ∑ i, lam i • gradient (P.g i) x + ∑ i, mu i • gradient (P.h i) x +
            ∑ i, a i • gradient (P.G i) x + ∑ i, b i • gradient (P.H i) x +
            ∑ i, c₁ i • (P.G i x • gradient (P.H i) x + P.H i x • gradient (P.G i) x) +
            ∑ i, c₂ i • (P.G i x • gradient (P.H i) x + P.H i x • gradient (P.G i) x) +
            ∑ i, d i • gradient (P.G i) x + ∑ i, e i • gradient (P.H i) x = 0 →
        lam = 0 ∧ mu = 0 ∧ a = 0 ∧ b = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ d = 0 ∧ e = 0 := by sorry

end MPECRelax.ScholtesMFCQ
