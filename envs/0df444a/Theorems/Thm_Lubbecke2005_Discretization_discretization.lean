-- Prove2me | Theorems.Thm_Lubbecke2005_Discretization_discretization
-- name    : Lubbecke2005.Discretization.discretization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T15:01:14.674084+00:00
-- url     : https://prove2.me/theorems/a666d4b5-172d-4022-b600-2060b7dcf753
-- title:
--   Theorem 1 (discretization) — $X = P \cap \mathbb{Z}^n$ is a finite union of integer points plus the monoid of finitely many integer rays
-- statement:
--   Let $D$ be an $m \times n$ matrix and $\mathbf d$ an $m$-vector with rational entries, let
--
--   $$
--   P = \{\mathbf x \in \mathbb R^n \mid D\mathbf x \geqslant \mathbf d,\ \mathbf x \geqslant \mathbf 0\} \neq \emptyset
--   $$
--
--   and $X = P \cap \mathbb Z^n$. Then there exist a finite set of integer points $\{\mathbf p_q\}_{q \in Q} \subseteq X$ and a finite set of integer rays $\{\mathbf p_r\}_{r \in R}$ of $P$ (nonzero integer vectors with $D\mathbf p_r \geqslant \mathbf 0$, $\mathbf p_r \geqslant \mathbf 0$) such that
--
--   $$
--   X = \Bigl\{\mathbf x \in \mathbb R^n_+ \ \Big|\ \mathbf x = \sum_{q \in Q} \mathbf p_q \lambda_q + \sum_{r \in R} \mathbf p_r \lambda_r,\ \ \sum_{q \in Q} \lambda_q = 1,\ \ \boldsymbol\lambda \in \mathbb Z_+^{|Q|+|R|}\Bigr\}. \qquad (24)
--   $$
--
--   Because the multipliers are nonnegative integers and $\sum_q \lambda_q = 1$, exactly one $\lambda_q$ equals $1$: every integer point of $P$ is one of the finitely many points $\mathbf p_q$ plus a nonnegative integer combination of the rays $\mathbf p_r$, and every such point is an integer point of $P$. This is the integer analogue of the Minkowski–Weyl representation (8) and is the basis of the discretization approach to Dantzig–Wolfe decomposition of integer programs, which yields the integer master problem (25). The paper cites Nemhauser and Wolsey (1988) for this result.
--
--   **Formalization Note** The paper does not say over which field $D$ and $\mathbf d$ are given; this statement **adds** that they are rational. Without it the theorem is false: $P = \{\mathbf x \in \mathbb R^2_+ \mid \sqrt 2\,x_1 - x_2 \geqslant 0\}$ has integer points $(k, \lfloor \sqrt2 k \rfloor)$ that no finite family of integer rays (all of slope $< \sqrt 2$) and base points can generate. The index sets are $Q = \{0,\dots,k-1\}$ and $R = \{0,\dots,l-1\}$ for some $k, l \in \mathbb N$ (either may be $0$; $k = 0$ exactly when $X = \emptyset$, which $P \neq \emptyset$ allows). The multiplier vector $\boldsymbol\lambda \in \mathbb Z_+^{|Q|+|R|}$ is written as a pair $(\lambda_Q, \lambda_R)$ of natural-number vectors. Both sides of (24) are sets of real vectors; $X$ is the set of points of $P$ with integer coordinates. "Integer rays" are not required to be extreme, as on the page.
-- source:
--   Lübbecke and Desrosiers, Selected Topics in Column Generation, Operations Research 53(6), 2005, pp. 1011–1012, Theorem 1, Eq. (24)

import Mathlib
import Definitions.Def_Lubbecke2005_Discretization_Polyhedron

namespace Lubbecke2005.Discretization

/-- **Lübbecke–Desrosiers 2005, Theorem 1 (§3.3, pp. 1011–1012), eq. (24).**
Let `P = {𝐱 ∈ ℝⁿ | D𝐱 ⩾ 𝐝, 𝐱 ⩾ 𝟎} ≠ ∅` with rational `D`, `𝐝` (an addition: the page
names no field, and the theorem fails for irrational data), and `X = P ∩ ℤⁿ`. Then there
are finitely many integer points `𝐩_q ∈ X` (`q ∈ Q = Fin k`) and finitely many integer
rays `𝐩_r` of `P` (`r ∈ R = Fin l`) such that
`X = {𝐱 ∈ ℝⁿ₊ | 𝐱 = Σ_q 𝐩_q λ_q + Σ_r 𝐩_r λ_r, Σ_q λ_q = 1, λ ∈ ℤ₊^{|Q|+|R|}}`. -/
theorem discretization {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (d : Fin m → ℚ)
    (hP : (polyhedronP D d).Nonempty) :
    ∃ (k l : ℕ) (p : Fin k → (Fin n → ℤ)) (w : Fin l → (Fin n → ℤ)),
      (∀ q, castVec (p q) ∈ integerPoints D d) ∧
      (∀ r, IsIntegerRay D (w r)) ∧
      integerPoints D d =
        {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧
          ∃ (lamQ : Fin k → ℕ) (lamR : Fin l → ℕ),
            ∑ q, lamQ q = 1 ∧
            x = ∑ q, (lamQ q : ℝ) • castVec (p q) + ∑ r, (lamR r : ℝ) • castVec (w r)} := by sorry

end Lubbecke2005.Discretization
