-- Prove2me | Theorems.Thm_KellyStochasticNetworks_RandomAccessCapacity_support_iff_strong_lagrangian
-- name    : KellyStochasticNetworks.RandomAccessCapacity.support_iff_strong_lagrangian
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:30.361321+00:00
-- url     : https://prove2.me/theorems/d344a1dc-55fb-453a-8af1-7507564fc6ff
-- title:
--   Theorem C.4 — support and the strong Lagrangian principle
-- statement:
--   Let $X\subseteq\mathbb R^n$, $f:\mathbb R^n\to\mathbb R$, $h:\mathbb R^n\to\mathbb R^m$, and $b\in\mathbb R^m$. Write
--
--   $$\phi(c)=\inf\{f(x):x\in X,\ h(x)=c\},\qquad L_b(x;y)=f(x)+\sum_i y_i(b_i-h_i(x)).$$
--
--   The following are equivalent: a finite-height nonvertical supporting hyperplane exists for $\phi$ at $b$, and the strong Lagrangian principle holds. Explicitly,
--
--   $$\begin{aligned}
--   &\exists a\in\mathbb R,\ y\in\mathbb R^m:\quad \phi(b)=a\ \text{ and }\ a+y^T(c-b)\le\phi(c)\ \text{for all }c\\
--   &\qquad\Longleftrightarrow\quad\exists y\in\mathbb R^m:\quad\phi(b)=\inf_{x\in X}L_b(x;y).
--   \end{aligned}$$
--
--   This is the source's equivalence connecting supports of a value function with multipliers attaining the dual value.
--
--   **Formalization Note** The faithful item retains the printed statement without adding feasibility or finiteness. All infima are extended-real. As recorded in finding F2, the literal statement is false for $X=\varnothing$: both infima are $+\infty$, while no finite-height support can touch $\phi(b)=+\infty$. The separately labelled corrected item adds precisely finiteness of $\phi(b)$.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 208 (PDF p. 216), Theorem C.4. DOI: 10.1017/cbo9781139565363.

import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Optimization

namespace KellyStochasticNetworks.RandomAccessCapacity

theorem support_iff_strong_lagrangian {n m : ℕ} (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → Fin m → ℝ)
    (b : Fin m → ℝ) :
    let φ : (Fin m → ℝ) → EReal := fun c =>
      sInf {v : EReal | ∃ x ∈ X, h x = c ∧ v = (f x : EReal)}
    (∃ a : ℝ, ∃ y : Fin m → ℝ, φ b = (a : EReal) ∧
      ∀ c, ((a + ∑ i, y i * (c i - b i) : ℝ) : EReal) ≤ φ c) ↔
    ∃ y : Fin m → ℝ, φ b =
      sInf {v : EReal | ∃ x ∈ X,
        v = ((f x + ∑ i, y i * (b i - h x i) : ℝ) : EReal)} := by sorry

end KellyStochasticNetworks.RandomAccessCapacity
