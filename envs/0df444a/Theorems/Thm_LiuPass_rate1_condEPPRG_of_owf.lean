-- Prove2me | Theorems.Thm_LiuPass_rate1_condEPPRG_of_owf
-- name    : LiuPass.rate1_condEPPRG_of_owf
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-20T22:40:55.459039+00:00
-- url     : https://prove2.me/theorems/acacaa39-2743-46c3-88bc-a12565d82e6e
-- title:
--   Theorem 5.6: rate-1 efficient condEP-PRGs from one-way functions
-- statement:
--   Theorem 5.6 of the paper. Assume one-way functions exist. Then for every $\gamma > 1$ there
--   exists a **rate-1 efficient** $\mu$-condEP-PRG
--   $$G : \{0,1\}^n \to \{0,1\}^{n + \gamma \log n}, \qquad \mu(n) = \frac{1}{n^2},$$
--   that is, one whose running time on inputs of length $n$ is $n + O(n^{\varepsilon})$ for some
--   constant $\varepsilon < 1$.
--
--   The construction is a padding trick applied to Theorem 5.5: on input $s_0 \| s_1$ with
--   $|s_1| = n^{1/2c_0}$ the generator outputs $s_0 \| G'(s_1)$, copying the long prefix untouched and
--   running the generator of Theorem 5.5 only on the short suffix, with the parameters
--   $\gamma' = 2c_0\gamma$ and $\delta' = 4c_0$ chosen so that the inherited indistinguishability gap
--   is exactly $1/n^2$. Rate-1 efficiency is what allows the average-case hardness of $K^t$ to be
--   obtained for *every* polynomial time bound $t(n) \ge (1+\varepsilon)n$ rather than only for
--   sufficiently large ones.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, p. 17, Theorem 5.6

import Definitions.Def_LiuPass_crypto
open Finset
open scoped Classical

namespace LiuPass

open Finset
open scoped Classical

theorem rate1_condEPPRG_of_owf (U : UMachine) (hf : ∃ f : BitStr → BitStr, IsOWF U f)
    (gamma : ℕ) (hgamma : 1 < gamma) :
    ∃ G : BitStr → BitStr,
      Rate1Efficient U G ∧ IsCondEPPRG U gamma (fun n => 1 / (n : ℝ) ^ 2) G := by sorry
end LiuPass
