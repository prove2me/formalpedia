-- Prove2me | Theorems.Thm_ModernConvex_SLemma_polyak_convexity
-- name    : ModernConvex.SLemma.polyak_convexity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:07.88875+00:00
-- url     : https://prove2.me/theorems/6f2ca11d-ad69-47ef-8aee-440108385fdc
-- title:
--   (SL.D) — Polyak's theorem: the joint range of three quadratic forms is closed and convex (n ≥ 3)
-- statement:
--   Let $n \ge 3$ and let $f_i(x) = x^TA_ix$, $i = 1, 2, 3$, be three homogeneous quadratic forms on $\mathbb R^n$ with symmetric $n\times n$ real matrices $A_i$. Assume that some linear combination $c_1A_1 + c_2A_2 + c_3A_3$ ($c_i \in \mathbb R$) is positive definite. Then the image of $\mathbb R^n$ under
--   $$F(x) = \begin{pmatrix} f_1(x) \\ f_2(x) \\ f_3(x)\end{pmatrix}$$
--   is a closed convex subset of $\mathbb R^3$.
--
--   This is B. T. Polyak's convexity theorem (1998), which extends Dines's theorem on the joint range of two quadratic forms to three. It is the tool behind the two-constraint S-lemma (SL.C).
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, $f_i(x)$ is `x ⬝ᵥ (A i *ᵥ x)`, and the index $i = 1,2,3$ is `i : Fin 3`; $F$ maps into `Fin 3 → ℝ`. Positive definiteness is Mathlib's `Matrix.PosDef`. The coefficients $c_i$ have arbitrary signs, as in the book's "a certain linear combination".
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 307, (SL.D) (Exercise 4.53)

import Mathlib

open Matrix

namespace ModernConvex.SLemma

/-- Ben-Tal–Nemirovski, (SL.D) (B. T. Polyak), p. 307: let `n ≥ 3` and `fᵢ(x) = xᵀAᵢx`,
`i = 1, 2, 3`, with symmetric `n × n` matrices `Aᵢ`, and assume a certain linear combination of
the `Aᵢ` is positive definite. Then the image of `ℝⁿ` under `F(x) = (f₁(x), f₂(x), f₃(x))` is a
closed convex set. The index `i = 1, 2, 3` is `i : Fin 3`. -/
theorem polyak_convexity {n : ℕ} (hn : 3 ≤ n) (A : Fin 3 → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hpd : ∃ c : Fin 3 → ℝ, (∑ i, c i • A i).PosDef) :
    IsClosed (Set.range fun x : Fin n → ℝ => fun i => x ⬝ᵥ (A i *ᵥ x)) ∧
      Convex ℝ (Set.range fun x : Fin n → ℝ => fun i => x ⬝ᵥ (A i *ᵥ x)) := by sorry

end ModernConvex.SLemma
