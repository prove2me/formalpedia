-- Prove2me | Theorems.Thm_ModernConvex_Spectral_convex_symmetric_doubly_stochastic_le
-- name    : ModernConvex.Spectral.convex_symmetric_doubly_stochastic_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:47.665465+00:00
-- url     : https://prove2.me/theorems/57dda89d-76db-43fd-ba0a-e89644004b6b
-- title:
--   (C) — a convex symmetric function does not increase under a double-stochastic matrix
-- statement:
--   Let $f : \mathbb R^m \to \mathbb R\cup\{+\infty\}$ be convex and symmetric, meaning that $f(x_{\sigma(1)},\dots,x_{\sigma(m)}) = f(x_1,\dots,x_m)$ for every permutation $\sigma$. Let $x \in \operatorname{Dom} f$, that is, $f(x) < +\infty$. Let $P$ be a double-stochastic $m\times m$ matrix: its entries are nonnegative and every row and every column sums to $1$. Then
--   $$f(Px) \le f(x).$$
--
--   The book calls this an immediate corollary of Birkhoff's theorem. It is the bridge from Birkhoff's theorem to eigenvalue inequalities such as $f(\operatorname{Dg}(A)) \le f(\lambda(A))$.
--
--   **Formalization Note** $f$ is `EReal`-valued, never $-\infty$, with a convex epigraph $\{(x,t) : f(x) \le t\} \subseteq \mathbb R^m\times\mathbb R$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 281, fact (C)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix

namespace ModernConvex.Spectral

/-- Ben-Tal–Nemirovski, fact (C), p. 281: let `f : ℝᵐ → ℝ ∪ {+∞}` be a convex symmetric function,
let `x ∈ Dom f` and let `P ∈ 𝒮_m` be double-stochastic. Then `f(Px) ≤ f(x)`. -/
theorem convex_symmetric_doubly_stochastic_le {m : ℕ} (f : (Fin m → ℝ) → EReal)
    (hf : IsConvexExt f) (hsym : IsSymmetricFn f) (x : Fin m → ℝ) (hx : f x ≠ ⊤)
    (P : Matrix (Fin m) (Fin m) ℝ) (hP : IsDoublyStochastic P) :
    f (P *ᵥ x) ≤ f x := by sorry

end ModernConvex.Spectral
