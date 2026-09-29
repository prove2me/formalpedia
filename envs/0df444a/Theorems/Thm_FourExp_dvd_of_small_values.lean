-- Prove2me | Theorems.Thm_FourExp_dvd_of_small_values
-- name    : FourExp.dvd_of_small_values
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T04:57:49.398171+00:00
-- url     : https://prove2.me/theorems/94ad0017-5959-42e3-8dbb-5279735f4026
-- title:
--   Two integer polynomials small at the same point share a factor
-- statement:
--   **A resultant argument: simultaneous small values force divisibility.**
--
--   Let $P, Q \in \mathbb{Z}[X]$ with $Q$ irreducible, let $\alpha \in \mathbb{C}$, and let $H, h \ge 1$ bound the coefficients of $P$ and of $Q$ respectively. Put $d = \deg P$ and $\delta = \deg Q$. If
--   $$\bigl((1 + |\alpha|)(d + \delta)\bigr)^{d+\delta}\; H^{\delta}\, h^{d}\; \bigl(|P(\alpha)| + |Q(\alpha)|\bigr) < 1,$$
--   then $Q$ divides $P$.
--
--   **Proof idea.** If $Q \nmid P$, then, $Q$ being irreducible, the two are coprime over $\mathbb{Q}$ (Gauss), so their resultant $R$ is a non-zero integer and $|R| \ge 1$. Write $R = A P + B Q$ with $A, B \in \mathbb{Z}[X]$ of degrees less than $\delta$ and $d$, whose coefficients are minors of the Sylvester matrix. Hadamard's inequality bounds them by $(d+\delta)^{d+\delta} H^{\delta} h^{d}$, up to the form above. Evaluating at $\alpha$ gives $|R| \le |A(\alpha)||P(\alpha)| + |B(\alpha)||Q(\alpha)|$, which is below $1$ under the hypothesis. A constant irreducible $Q = \pm p$ is covered as well: then the left-hand side is at least $p \ge 2$.
--
--   **What it is for.** Step (3.13) of Waldschmidt's proof of `FourExp.transcendence_criterion_continuous`. It shows $Q_q \mid P_N$ for $N = \lfloor z_q \rfloor$.
-- source:
--   Resultant bound as used in M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §3, inequality (3.13), citing S. Lang, Introduction to Transcendental Numbers, 1966, V §2.

import Mathlib

namespace FourExp

theorem dvd_of_small_values
    (P Q : Polynomial ℤ) (hQ : Irreducible Q) (α : ℂ) (H h : ℝ) (hH : 1 ≤ H) (hh : 1 ≤ h)
    (hPH : ∀ i : ℕ, |(P.coeff i : ℝ)| ≤ H) (hQh : ∀ i : ℕ, |(Q.coeff i : ℝ)| ≤ h)
    (hsmall : ((1 + ‖α‖) * ((P.natDegree + Q.natDegree : ℕ) : ℝ)) ^ (P.natDegree + Q.natDegree)
        * H ^ Q.natDegree * h ^ P.natDegree
        * (‖Polynomial.aeval α P‖ + ‖Polynomial.aeval α Q‖) < 1) :
    Q ∣ P := by
  sorry

end FourExp
