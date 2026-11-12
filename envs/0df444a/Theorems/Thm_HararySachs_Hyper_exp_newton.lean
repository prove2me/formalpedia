-- Prove2me | Theorems.Thm_HararySachs_Hyper_exp_newton
-- name    : HararySachs.Hyper.exp_newton
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T05:16:41.95545+00:00
-- url     : https://prove2.me/theorems/fc8fa87b-96ed-4204-9656-d476638436b5
-- title:
--   Exponential (Newton) recursion characterises the Schur polynomials $P_d$
-- statement:
--   Let $t = (t_1, t_2, \dots)$ be a sequence of rationals. Let $P_d(t)$ be the Schur polynomial of the mission (Definition 2), that is, the coefficient of $z^d$ in $\exp\big(\sum_{j\ge 1} t_j z^j\big)$:
--   $$P_0(t) = 1, \qquad P_d(t) = \sum_{m=1}^{d} \frac{1}{m!} \sum_{\substack{a_1+\dots+a_m = d\\ a_i \ge 1}} t_{a_1}\cdots t_{a_m} \quad (d \ge 1).$$
--   Let $D \ge 0$, and let $c_0, c_1, \dots$ be rationals with $c_0 = 1$ satisfying the Newton-type recursion
--   $$d\, c_d = \sum_{j=1}^{d} j\, t_j\, c_{d-j} \qquad (1 \le d \le D).$$
--   Then $c_d = P_d(t)$ for every $d \le D$.
--
--   This is the coefficientwise form of the fact that $F(z) = \exp(T(z))$ is the unique power series with $F(0)=1$ and $zF'(z) = zT'(z)\,F(z)$. Applied with $t_j = -\mathrm{Tr}_j/j$, it converts Newton's identities between the coefficients of the characteristic polynomial and the traces into the closed form required by `trace_identity`.
-- source:
--   Clark–Cooper, A Harary–Sachs theorem for hypergraphs, arXiv:1812.00468v2, Definition 2 (Schur polynomials $P_d$) and the exponential formula preceding Theorem 14; standard (e.g. Stanley, Enumerative Combinatorics Vol. 2, Section 5.1).

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators

namespace HararySachs.Hyper

theorem exp_newton (D : ℕ) (t c : ℕ → ℚ) (h0 : c 0 = 1)
    (hrec : ∀ d, 1 ≤ d → d ≤ D →
      (d : ℚ) * c d = ∑ j ∈ Finset.Icc 1 d, (j : ℚ) * t j * c (d - j)) :
    ∀ d ≤ D, c d = schurP d t := by sorry

end HararySachs.Hyper
