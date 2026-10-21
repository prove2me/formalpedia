-- Prove2me | Theorems.Thm_LootBox_TB_eq_16
-- name    : LootBox.TB.eq_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:50.497867+00:00
-- url     : https://prove2.me/theorems/18d933b1-4d5b-4c99-94f3-512626b62be5
-- title:
--   Eq. (16), p. 33 (index corrected) — R_TB(p) = p · E[Σ_{k=r}^{N} 1/k], r the first passage of the i.i.d. walk above Np
-- statement:
--   Let $F$ be a valuation law as in the model (non-negative, finite variance), $N \ge 1$, and $p > 0$. Let $w_0, w_1, \dots$ be i.i.d. with law $F$ and let $r = \inf\{ j \ge 1 : Np \le w_0 + \dots + w_{j-1} \}$ be the first passage of their partial sums above $Np$. Then the normalized revenue of the traditional box at price $p$ is
--
--   $$R_{TB}(p) = p \; \mathbb E\Big[ \sum_{k=r}^{N} \frac1k \Big],$$
--
--   where the sum is empty (zero) when $r > N$ or $r = \infty$.
--
--   This is the revenue identity on which both bounds of Theorem 3 rest: the stopping behaviour of the myopic customer is encoded by a single first-passage time of a random walk, and the expected number of boxes by a harmonic tail.
--
--   **Formalization Note** The page writes the tail as $\log N + \gamma + \zeta_N - \log(N-\tau_N+1) - \gamma - \zeta_{N-\tau_N+1} = H_N - H_{N-\tau_N+1}$, which omits the term $k = r_N = N - \tau_N + 1$. The middle line of (16), $\frac1N(1 + \frac{N}{N-1} + \dots + \frac{N}{N-\tau_N+1})$, equals the tail from $k = r_N$, and that is the statement posed here. With the printed index the identity is false: for $V \equiv 1$, $N = 1$ and $0 < p \le 1$ the revenue is $p$, but the printed tail is $0$. The page's backward walk $C_j$ (built from $V_N, V_{N-1}, \dots$ and virtual i.i.d. variables) is represented by the partial sums of an i.i.d. sequence with the same law.
-- source:
--   Chen, Elmachtoub, Hamilton & Lei, Loot Box Pricing and Design, manuscript submitted August 2019 (Management Science doi:10.1287/mnsc.2020.3748), proof of Theorem 3, Eq. (16), p. 33 (with r_N = N − τ_N + 1, p. 33), index corrected

import Mathlib
import Definitions.Def_LootBox_TB_Setting

namespace LootBox.TB

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem eq_16 (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) (N : ℕ) [NeZero N]
    (p : ℝ) (hp : 0 < p) :
    revenue F N p =
      ENNReal.ofReal p *
        ∫⁻ w, ENNReal.ofReal (harmTail N (firstPassage w ((N : ℝ) * p))) ∂(walkLaw F) := by sorry

end LootBox.TB
