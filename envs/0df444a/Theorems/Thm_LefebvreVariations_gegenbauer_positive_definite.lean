-- Prove2me | Theorems.Thm_LefebvreVariations_gegenbauer_positive_definite
-- name    : LefebvreVariations.gegenbauer_positive_definite
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T21:53:59.071397+00:00
-- url     : https://prove2.me/theorems/da6d8c66-3b61-4e0b-97c4-5424e64fd02c
-- title:
--   Lefebvre's variations, No. 3 — on a theme by Schoenberg: Gegenbauer polynomials are positive definite on the sphere (Schoenberg)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   This is Schoenberg's theorem that the Gegenbauer (ultraspherical) polynomials are positive definite on the unit sphere, stated for finite point sets.
--
--   Let $n \ge 3$ and $\alpha = \frac{n-2}{2}$. For $k \ge 0$ let $C_k^{(\alpha)}$ be the Gegenbauer polynomial of degree $k$,
--
--   $$
--   C_k^{(\alpha)}(t) \;=\; \sum_{m=0}^{\lfloor k/2 \rfloor} (-1)^m \, \frac{(\alpha)_{k-m}}{m!\,(k-2m)!}\,(2t)^{k-2m},
--   \qquad (\alpha)_j = \alpha(\alpha+1)\cdots(\alpha+j-1),
--   $$
--
--   so that $C_0^{(\alpha)} = 1$, $C_1^{(\alpha)}(t) = 2\alpha t$, $C_2^{(\alpha)}(t) = 2\alpha(\alpha+1)t^2 - \alpha$, and $\sum_k C_k^{(\alpha)}(t)\,r^k = (1-2rt+r^2)^{-\alpha}$. Then for every finite set $S$ of unit vectors in $\mathbb{R}^n$,
--
--   $$
--   \sum_{x \in S} \sum_{y \in S} C_k^{(\alpha)}\bigl(\langle x, y\rangle\bigr) \;\ge\; 0 .
--   $$
--
--   Equivalently, the Gram-type matrix $\bigl(C_k^{(\alpha)}(\langle x_i, x_j\rangle)\bigr)_{i,j}$ has nonnegative total sum for every finite family of distinct points of $S^{n-1}$. The classical proof writes $C_k^{(\alpha)}(\langle x,y\rangle)$ as a positive multiple of $\sum_{\ell} Y_\ell(x)\,Y_\ell(y)$ for an orthonormal basis $(Y_\ell)$ of spherical harmonics of degree $k$ (the addition theorem), so the double sum equals a positive multiple of $\sum_\ell \bigl(\sum_{x\in S} Y_\ell(x)\bigr)^2$.
--
--   This inequality is the analytic input of the Delsarte linear-programming bound for spherical codes. In dimension $8$, the polynomial $f(t) = (t+1)(t+\tfrac12)^2 t^2 (t-\tfrac12)$ satisfies $f \le 0$ on $[-1, \tfrac12]$ and $f = \sum_{k=0}^{6} f_k C_k^{(3)}$ with $f_0 = \tfrac{3}{320}$ and all $f_k > 0$, so the theorem above gives $f_0 N^2 \le N f(1) = \tfrac94 N$ for any kissing configuration of $N$ points in $\mathbb{R}^8$, that is $N \le 240$.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin n)` and the set is a `Finset` of unit vectors (`‖x‖ = 1`); the inner product is `inner ℝ x y`. The Gegenbauer polynomial is written out inline by the explicit sum above: the Pochhammer symbol $(\alpha)_j$ is `(ascPochhammer ℝ j).eval α` with `α = ((n : ℝ) - 2) / 2`, the upper summation index is `k / 2` (natural-number division) and the exponents `k - m`, `k - 2 * m` are natural-number subtractions, which never truncate on the range $m \le \lfloor k/2 \rfloor$. The hypothesis $n \ge 3$ excludes $n = 2$, where $\alpha = 0$ and the formula degenerates to $0$ for $k \ge 1$, and $n = 1$, where the statement is false ($k = 1$ gives $-(\sum_{x} x)^2$).
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `KissingNumber.kissing_number_eight` ($\tau(8) = 240$). The lower bound $\tau(8) \ge 240$ comes from the $240$ roots of $E_8$, and the upper bound from Delsarte's linear-programming argument with Levenshtein's polynomial, whose expansion in Gegenbauer polynomials has positive coefficients. The one analytic input of that argument is this statement. It is not a special case of the base problem: it is a classical theorem about spheres (Schoenberg 1942) that is the single missing ingredient of a verified proof of the base statement.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). I. J. Schoenberg, Positive definite functions on spheres, Duke Math. J. 9 (1942), 96–108 (positive definiteness of the Gegenbauer polynomials C_k^{((n-2)/2)} on S^{n-1}). Also: P. Delsarte, J.-M. Goethals, J. J. Seidel, Spherical codes and designs, Geom. Dedicata 6 (1977), 363–388; J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, Chapter 9 and Chapter 13; E. M. Stein and G. Weiss, Introduction to Fourier Analysis on Euclidean Spaces, Chapter IV (addition theorem for zonal harmonics). The dimension-8 certificate f(t) = (t+1)(t+1/2)^2 t^2 (t-1/2) is from V. I. Levenshtein, On bounds for packings in n-dimensional Euclidean space, Soviet Math. Dokl. 20 (1979), 417–421, and A. M. Odlyzko and N. J. A. Sloane, New bounds on the number of unit spheres that can touch a unit sphere in n dimensions, J. Combin. Theory Ser. A 26 (1979), 210–214. Origin of this statement: it is the missing step of a reduction of KissingNumber.kissing_number_eight (τ(8) = 240). In that reduction everything else is proved in Lean: the lower bound τ(8) ≥ 240 by the 240 roots of E8 (checked by kernel computation), and the upper bound τ(8) ≤ 240 by Delsarte's linear-programming argument with the Levenshtein polynomial, whose exact expansion f = 3/320 C_0 + 1/80 C_1 + 5/448 C_2 + 39/4480 C_3 + 19/3840 C_4 + 1/448 C_5 + 1/1792 C_6 in the polynomials C_k^{(3)} is verified by `ring`. The reduction uses the statement only for n = 8 and 1 ≤ k ≤ 6.

import Definitions.Def_KissingNumber

set_option autoImplicit false

namespace LefebvreVariations
theorem gegenbauer_positive_definite (n : ℕ) (hn : 3 ≤ n) (k : ℕ)
    (s : Finset (EuclideanSpace ℝ (Fin n))) (hs : ∀ x ∈ s, ‖x‖ = 1) :
    0 ≤ ∑ x ∈ s, ∑ y ∈ s, ∑ m ∈ Finset.range (k / 2 + 1),
      (-1 : ℝ) ^ m * (ascPochhammer ℝ (k - m)).eval (((n : ℝ) - 2) / 2) /
        ((m.factorial : ℝ) * ((k - 2 * m).factorial : ℝ)) * (2 * inner ℝ x y) ^ (k - 2 * m) := by sorry
end LefebvreVariations
