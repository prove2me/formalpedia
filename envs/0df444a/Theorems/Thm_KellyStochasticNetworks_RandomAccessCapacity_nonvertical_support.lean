-- Prove2me | Theorems.Thm_KellyStochasticNetworks_RandomAccessCapacity_nonvertical_support
-- name    : KellyStochasticNetworks.RandomAccessCapacity.nonvertical_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:24.506464+00:00
-- url     : https://prove2.me/theorems/870a8eee-d991-4eef-a663-d1b524076d72
-- title:
--   Theorem C.3 — nonvertical support at an interior finite point
-- statement:
--   Let $\phi:\mathbb R^m\to[-\infty,+\infty]$ be convex, in the sense that its real epigraph is convex. Suppose $b$ belongs to the ordinary Euclidean interior of the set where $\phi$ is finite. Then there exist $a\in\mathbb R$ and $y\in\mathbb R^m$ such that
--
--   $$\phi(b)=a,\qquad a+\sum_i y_i(c_i-b_i)\le\phi(c)\quad\text{for every }c\in\mathbb R^m.$$
--
--   Thus an affine minorant touches the function at $b$, defining a nonvertical supporting hyperplane. The result supplies finite multipliers rather than a potentially vertical support to an epigraph.
--
--   **Formalization Note** Interior is taken in the entire finite-dimensional space, not relative interior. Finiteness is expressed by equality to an embedded real number, and affine heights are evaluated in the reals before comparison with extended values.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 208 (PDF p. 216), Theorem C.3. DOI: 10.1017/cbo9781139565363.

import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Optimization

namespace KellyStochasticNetworks.RandomAccessCapacity

theorem nonvertical_support {m : ℕ} (φ : (Fin m → ℝ) → EReal)
    (hconv : Convex ℝ {p : (Fin m → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)})
    (b : Fin m → ℝ)
    (hb : b ∈ interior {c | ∃ a : ℝ, φ c = (a : EReal)}) :
    ∃ a : ℝ, ∃ y : Fin m → ℝ, φ b = (a : EReal) ∧
      ∀ c, ((a + ∑ i, y i * (c i - b i) : ℝ) : EReal) ≤ φ c := by sorry

end KellyStochasticNetworks.RandomAccessCapacity
