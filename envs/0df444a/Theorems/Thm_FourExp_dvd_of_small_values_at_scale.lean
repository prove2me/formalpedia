-- Prove2me | Theorems.Thm_FourExp_dvd_of_small_values_at_scale
-- name    : FourExp.dvd_of_small_values_at_scale
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:15:55.102729+00:00
-- url     : https://prove2.me/theorems/d720908d-8850-4491-a909-d3cc6d5a732a
-- title:
--   One scale of Gel'fond's criterion: small values at the same point force divisibility
-- statement:
--   Let $\alpha \in \mathbb{C}$ and $\varepsilon > 0$. There is $U$ such that, for all real $u \ge U$ and $1 \le v \le u$, the following holds. Let $P, Q \in \mathbb{Z}[X]$ with $Q$ irreducible, and suppose:
--
--   - the coefficients of $P$ are at most $e^{u}$ in absolute value, and $\deg P \le v$;
--   - the coefficients of $Q$ are at most $e^{3u}$ in absolute value, and $\deg Q \le (1 + \varepsilon/2)\, v$;
--   - $|P(\alpha)| < e^{-(4+\varepsilon)uv}$ and $|Q(\alpha)| < e^{-(4+\varepsilon)uv}$.
--
--   Then $Q$ divides $P$.
--
--   This is `FourExp.dvd_of_small_values` with every size written in terms of one scale $(u, v)$, the form in which the proof of the transcendence criterion uses it at each step.
-- source:
--   A step in the proof of the transcendence criterion FourExp.transcendence_criterion_continuous (M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §3). Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

open Polynomial

namespace FourExp

theorem dvd_of_small_values_at_scale (α : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : ℝ, ∀ u v : ℝ, U ≤ u → 1 ≤ v → v ≤ u → ∀ P Q : ℤ[X], Irreducible Q →
      (∀ i, |(P.coeff i : ℝ)| ≤ Real.exp u) → (P.natDegree : ℝ) ≤ v →
      (∀ i, |(Q.coeff i : ℝ)| ≤ Real.exp (3 * u)) → (Q.natDegree : ℝ) ≤ (1 + ε / 2) * v →
      ‖aeval α P‖ < Real.exp (-((4 + ε) * (u * v))) →
      ‖aeval α Q‖ < Real.exp (-((4 + ε) * (u * v))) → Q ∣ P := by
  sorry

end FourExp
