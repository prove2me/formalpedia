-- Prove2me | Theorems.Thm_LefebvreVariations_algebraic_mul_pow_sub_pow_finite
-- name    : LefebvreVariations.algebraic_mul_pow_sub_pow_finite
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:02:57.4303+00:00
-- url     : https://prove2.me/theorems/4530a6c6-33dd-483c-800d-01b7033687fc
-- title:
--   Lefebvre's variations, No. 8 — on a theme by Adamczewski and Bugeaud: algebraic irrationals stay far from integers after multiplication by $b^{r+s}-b^r$ (the Diophantine step of Adamczewski–Bugeaud)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $\xi$ be a real algebraic irrational number, let $b \ge 2$ be an integer and let $\varepsilon > 0$. Then there are only finitely many triples $(r, s, p)$ with $r \ge 0$, $s \ge 1$ integers and $p \in \mathbb{Z}$ such that
--
--   $$
--   \bigl|\, \xi\,(b^{r+s} - b^{r}) - p \,\bigr| \;<\; b^{-\varepsilon (r+s)} .
--   $$
--
--   Equivalently, the numbers $\xi\, b^{r}(b^{s}-1)$ stay away from the integers at an exponential rate: for all but finitely many pairs $(r,s)$ with $s\ge1$, the distance from $\xi\,(b^{r+s}-b^{r})$ to the nearest integer is at least $b^{-\varepsilon(r+s)}$.
--
--   This is the Diophantine input of the theorem of Adamczewski and Bugeaud (Ann. of Math. 2007) that the complexity $p(n)$ of the base-$b$ expansion of an irrational algebraic number satisfies $\liminf_{n\to\infty} p(n)/n = +\infty$. It follows from the $p$-adic Subspace Theorem of Schmidt and Schlickewei applied to the points $(b^{r+s}, b^{r}, p) \in \mathbb{Z}^3$, with the linear forms $X_1,\ X_2,\ \xi X_1 - \xi X_2 - X_3$ at the infinite place and $X_1, X_2, X_3$ at the primes dividing $b$, together with Ridout's theorem for the solutions lying in the planes $a_1X_1 + a_2X_2 = 0$. Two equal blocks of $n$ digits at positions $r$ and $r+s$ of the expansion of $\xi$ give exactly such an approximation with error less than $b^{-n}$; if $p(n) < Kn$ infinitely often, the pigeonhole principle produces such blocks with $r + s < Kn$, hence infinitely many triples for $\varepsilon = 1/K$.
--
--   **Formalization Note** The triples are elements `t = (r, s, p)` of `ℕ × ℕ × ℤ`, written `t.1`, `t.2.1`, `t.2.2`. The bound $b^{-\varepsilon(r+s)}$ is the real power `(b : ℝ) ^ (-(ε * (r + s)))` (`Real.rpow`, with $r+s$ cast through `ℕ`). Algebraicity is `IsAlgebraic ℚ ξ` and irrationality is Mathlib's `Irrational ξ`; both hypotheses are needed (for rational $\xi = u/v$ the triples with $v \mid b^{r}(b^{s}-1)$ give infinitely many exact solutions). No upper bound on $r/s$ is imposed.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `BorelNormality.adamczewski_bugeaud_complexity` (the base-$b$ expansion of an irrational algebraic number has $p(n)/n \to \infty$). A pigeonhole argument on repeated blocks of digits turns a bounded $\liminf p(n)/n$ into infinitely many triples $(r,s,p)$ with $|\xi(b^{r+s}-b^r)-p| < b^{-\varepsilon(r+s)}$. This statement says there are only finitely many such triples, which is the Diophantine step (a consequence of the Subspace Theorem). It is not a special case of the base statement: it is the number-theoretic ingredient from which the base statement follows by the verified combinatorial reduction.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). B. Adamczewski, Y. Bugeaud, On the complexity of algebraic numbers I. Expansions in integer bases, Ann. of Math. (2) 165 (2007), 547–565 (the proof of their combinatorial transcendence criterion applies the Subspace Theorem to exactly the points (b^{r+s}, b^r, p) and the linear forms above); B. Adamczewski, Y. Bugeaud, F. Luca, Sur la complexité des nombres algébriques, C. R. Acad. Sci. Paris 339 (2004), 11–14. The underlying theorems: H. P. Schlickewei, The p-adic Thue–Siegel–Roth–Schmidt theorem, Arch. Math. 29 (1977), 267–270 (p-adic Subspace Theorem; see also W. M. Schmidt, Diophantine Approximation, LNM 785, and Y. Bugeaud, Approximation by Algebraic Numbers, Cambridge Tracts in Math. 160, 2004, Chapter 2); D. Ridout, The p-adic generalization of the Thue–Siegel–Roth theorem, Mathematika 5 (1958), 40–48. Origin of this statement: it is the missing step of a reduction of BorelNormality.adamczewski_bugeaud_complexity (open milestone of BorelNormality.borel_conjecture). The reduction, verified in Lean, uses the pigeonhole principle on the p(n)+1 blocks of length n starting at positions 0..p(n), the identity floor(ξ b^(i+n)) = b^n floor(ξ b^i) + (value of the n digits at i), and the irrationality of ξ.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem algebraic_mul_pow_sub_pow_finite (ξ : ℝ) (hξ : IsAlgebraic ℚ ξ) (hi : Irrational ξ)
    (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    {t : ℕ × ℕ × ℤ | 1 ≤ t.2.1 ∧
      |ξ * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2| <
        (b : ℝ) ^ (-(ε * ((t.1 + t.2.1 : ℕ) : ℝ)))}.Finite := by sorry
end LefebvreVariations
