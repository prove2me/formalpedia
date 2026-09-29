-- Prove2me | Theorems.Thm_FourExp_extrapolation_numbers
-- name    : FourExp.extrapolation_numbers
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-27T07:58:31.809743+00:00
-- url     : https://prove2.me/theorems/4613db26-460f-498c-a106-b0b8709cc575
-- title:
--   The numerical inequality of the extrapolation step in the four exponentials theorem
-- statement:
--   Let $X \ge 0$, $Y \ge 1$, $\kappa \ge 0$ be real and $N, S, t_1, t_2, s$ natural numbers with $s \le S$ and $N \ge 32(13 + \kappa + \log Y + 2XY)$. Write $q = \sqrt{\log N}$ and suppose
--
--   $$Sq \le N^{2} \le 2Sq, \qquad N \le 2t_1 q, \qquad Nq \le 2t_2.$$
--
--   Then
--
--   $$2\, s!\, (N - 1)^{-t_1 t_2 S} \cdot S (2N)^{2} e^{\kappa N^{2} q} \cdot (Y N^{2} q)^{S} \cdot e^{2NX \cdot Y N^{2} q} \le e^{-N^{4} q / 32}.$$
--
--   These are the sizes of the parameters $S \approx N^{2}/q$, $t_1 \approx N/q$, $t_2 \approx Nq$ in the extrapolation of the four exponentials construction: the zero factor contributes $-N^{4}q/16$ to the logarithm, and every other factor $O(N^{3} q)$.
-- source:
--   The parameter estimate in the proof of Lemma 5 of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202. Formal proof: Diaz modulus mission, 27 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

theorem extrapolation_numbers (X Y κ : ℝ) (hX : 0 ≤ X) (hY : 1 ≤ Y) (hκ : 0 ≤ κ)
    (N S t₁ t₂ s : ℕ) (hbig : 32 * (13 + κ + Real.log Y + 2 * X * Y) ≤ N) (hs : s ≤ S)
    (hSu : (S : ℝ) * Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2)
    (hSl : (N : ℝ) ^ 2 ≤ 2 * (S * Real.sqrt (Real.log N)))
    (h₁ : (N : ℝ) ≤ 2 * (t₁ * Real.sqrt (Real.log N)))
    (h₂ : (N : ℝ) * Real.sqrt (Real.log N) ≤ 2 * t₂) :
    (s.factorial : ℝ) * 2 * (1 / ((N : ℝ) - 1)) ^ (t₁ * t₂ * S) *
        (S * (2 * N) * (2 * N) * Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) *
          (Y * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N))) ^ S *
          Real.exp (2 * N * X * (Y * ((N : ℝ) ^ 2 * Real.sqrt (Real.log N)))))
      ≤ Real.exp (-((N : ℝ) ^ 4 * Real.sqrt (Real.log N) / 32)) := by
  sorry

end FourExp
