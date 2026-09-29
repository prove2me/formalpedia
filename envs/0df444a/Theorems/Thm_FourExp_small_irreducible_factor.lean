-- Prove2me | Theorems.Thm_FourExp_small_irreducible_factor
-- name    : FourExp.small_irreducible_factor
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T04:57:45.288583+00:00
-- url     : https://prove2.me/theorems/0d10482b-a0ff-46c6-a565-57809008dcf0
-- title:
--   Gel'fond's lemma: a polynomial small at a transcendental number has a small irreducible factor
-- statement:
--   **Small values pass to an irreducible factor.**
--
--   Let $\alpha$ be transcendental and let $P \in \mathbb{Z}[X]$ be primitive, with all coefficients at most $H$ in absolute value. Let $n$ and $\lambda$ be real with $\deg P \le n \le \log H$ and $\lambda > 6$. If
--   $$|P(\alpha)| < H^{-\lambda n},$$
--   then there are a primitive irreducible divisor $Q$ of $P$ and an integer $s \ge 1$ with
--   $$|Q(\alpha)| < H^{-(\lambda - 6)n/s}, \qquad |\text{coefficients of } Q| \le H^{1/s} e^{2n/s}, \qquad \deg Q \le n/s .$$
--
--   **Proof idea.** Factor $P$ into irreducibles, grouped as powers $Q_1^{e_1}\cdots Q_r^{e_r}$. Gel'fond's height inequality bounds $\prod_i H(Q_i)^{e_i}$ by $e^{n} H$. Since $|P(\alpha)| = \prod_i |Q_i(\alpha)|^{e_i}$ is very small, a weighted averaging argument finds one factor that is small relative to its own share of the degree and the height. Here $s$ is essentially the multiplicity with which that share is taken.
--
--   **What it is for.** Step (3.7) of Waldschmidt's proof of `FourExp.transcendence_criterion_continuous`. It is applied to the primitive part of each $P_q$, with $H = e^{\sigma_1(q)}$, $n = \sigma_2(q)$ and $\lambda = C$.
-- source:
--   M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §3, Lemme 2 (A. O. Gel'fond, Transcendental and Algebraic Numbers, 1952; compare S. Lang, Introduction to Transcendental Numbers, 1966, VI §2).

import Mathlib

namespace FourExp

theorem small_irreducible_factor
    (α : ℂ) (hα : Transcendental ℚ α) (P : Polynomial ℤ) (hprim : P.IsPrimitive)
    (H n lam : ℝ) (hPH : ∀ i : ℕ, |(P.coeff i : ℝ)| ≤ H)
    (hlog : n ≤ Real.log H) (hdeg : (P.natDegree : ℝ) ≤ n) (hlam : 6 < lam)
    (hsmall : ‖Polynomial.aeval α P‖ < H ^ (-(lam * n))) :
    ∃ Q : Polynomial ℤ, Q ∣ P ∧ Q.IsPrimitive ∧ Irreducible Q ∧
      ∃ s : ℕ, 0 < s ∧
        ‖Polynomial.aeval α Q‖ < H ^ (-((lam - 6) * n / s)) ∧
        (∀ i : ℕ, |(Q.coeff i : ℝ)| ≤ H ^ ((1 : ℝ) / s) * Real.exp (2 * n / s)) ∧
        (Q.natDegree : ℝ) ≤ n / s := by
  sorry

end FourExp
