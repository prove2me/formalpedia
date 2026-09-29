-- Prove2me | Theorems.Thm_FourExp_height_dvd_le
-- name    : FourExp.height_dvd_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T04:57:47.964187+00:00
-- url     : https://prove2.me/theorems/5b99493b-fb4c-49c3-8afe-4ed79a8f2bed
-- title:
--   Gel'fond's height bound for a divisor of an integer polynomial
-- statement:
--   **The height of a divisor is controlled by the height of the multiple.**
--
--   Let $P \in \mathbb{Z}[X]$ be non-zero, and let $Q \in \mathbb{Z}[X]$ divide $P$. If every coefficient of $P$ has absolute value at most $H$, then every coefficient of $Q$ has absolute value at most
--   $$e^{\deg P}\, H .$$
--
--   **Proof idea.** Gel'fond's inequality states $H(P_1)\,H(P_2) \le e^{\deg(P_1P_2)}\,H(P_1P_2)$ for complex polynomials, where $H$ is the largest absolute value of a coefficient. It follows from comparing heights with Mahler measure, using $M(P_1P_2) = M(P_1)M(P_2)$ and $H(P) \le 2^{\deg P} M(P)$ together with $M(P) \le \sqrt{\deg P + 1}\,H(P)$. Writing $P = QR$ with $R \in \mathbb{Z}[X]$ non-zero gives $H(R) \ge 1$, hence $H(Q) \le e^{\deg P} H(P)$.
--
--   **What it is for.** In the proof of `FourExp.transcendence_criterion_continuous`, once the small factor $Q_q$ is known to divide $P_N$, this bounds its height by the size of $P_N$. That is what contradicts the minimality of the scale $z_q$.
-- source:
--   M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §3, Lemme 1 (A. O. Gel'fond; a generalisation of a lemma of Popken and Koksma).

import Mathlib

namespace FourExp

theorem height_dvd_le
    (P Q : Polynomial ℤ) (hP : P ≠ 0) (hQP : Q ∣ P) (H : ℝ)
    (hPH : ∀ i : ℕ, |(P.coeff i : ℝ)| ≤ H) :
    ∀ i : ℕ, |(Q.coeff i : ℝ)| ≤ Real.exp (P.natDegree : ℝ) * H := by
  sorry

end FourExp
