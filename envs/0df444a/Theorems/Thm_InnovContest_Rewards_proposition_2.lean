-- Prove2me | Theorems.Thm_InnovContest_Rewards_proposition_2
-- name    : InnovContest.Rewards.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:19.36939+00:00
-- url     : https://prove2.me/theorems/9819a4b9-928b-437d-8dfd-5677539053a8
-- title:
--   Proposition 2 — binomial participation count
-- statement:
--   Consider a feasible contest allocation, a nonnegative entry cost $c_p$, and the corresponding entry threshold $a_{\min}$. Each solver enters when their ability is at least $a_{\min}$. If $N$ is the number entering, then for every $0\le k\le n$,
--
--   $$\Pr\{N=k\}=\binom nk(1-F(a_{\min}))^kF(a_{\min})^{n-k}.$$
--
--   Thus $N$ is binomial with entry probability $1-F(a_{\min})$; in particular the failure probability is its $k=0$ case.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version), p. 9, Proposition 2, equation (5)

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

namespace InnovContest.Rewards

/-- Proposition 2, p. 9: the number of entrants has the binomial distribution. -/
theorem proposition_2 (M : AbilityModel) (budget cp : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) (hcp : 0 ≤ cp) (k : ℕ) (hk : k ≤ M.n) :
    (profileLaw M).real
      {A | ((Finset.univ : Finset (Fin M.n)).filter
        (fun i => amin M r cp ≤ A i)).card = k} =
      (M.n.choose k : ℝ) * (1 - M.F (amin M r cp)) ^ k *
        (M.F (amin M r cp)) ^ (M.n - k) := by sorry

end InnovContest.Rewards
