-- Prove2me | Theorems.Thm_KellyStochasticNetworks_RandomAccessCapacity_inequality_value_convex
-- name    : KellyStochasticNetworks.RandomAccessCapacity.inequality_value_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:24.134441+00:00
-- url     : https://prove2.me/theorems/f603850a-3b30-450c-a4d8-b2ff99aec571
-- title:
--   Theorem C.7 — convexity of the inequality value function
-- statement:
--   Let $X\subseteq\mathbb R^n$ be convex. Suppose $f:\mathbb R^n\to\mathbb R$ and every component of $h:\mathbb R^n\to\mathbb R^m$ are convex on $X$. Define the extended value of the slack-variable problem by
--
--   $$\phi(b)=\inf\{f(x):x\in X,\ h_i(x)\le b_i\text{ for every }i\}.$$
--
--   Then $\phi$ is convex, equivalently
--
--   $$\{(b,t)\in\mathbb R^m\times\mathbb R:\phi(b)\le t\}\text{ is convex}.$$
--
--   This supplies convexity of the perturbed value function for the supporting-hyperplane result.
--
--   **Formalization Note** Eliminating the nonnegative slack vector in (C.2) gives precisely $h(x)\le b$. Infima live in the extended real line; no feasibility, attainment, or finite-optimum hypothesis is added. Empty feasible sets and values unbounded below retain their respective infinite values.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 209 (PDF p. 217), Theorem C.7. DOI: 10.1017/cbo9781139565363.

import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Optimization

namespace KellyStochasticNetworks.RandomAccessCapacity

theorem inequality_value_convex {n m : ℕ} (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → Fin m → ℝ)
    (hX : Convex ℝ X) (hf : ConvexOn ℝ X f)
    (hh : ∀ i, ConvexOn ℝ X (fun x => h x i)) :
    let φ : (Fin m → ℝ) → EReal := fun b =>
      sInf {v : EReal | ∃ x ∈ X, (∀ i, h x i ≤ b i) ∧ v = (f x : EReal)}
    Convex ℝ {p : (Fin m → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by sorry

end KellyStochasticNetworks.RandomAccessCapacity
