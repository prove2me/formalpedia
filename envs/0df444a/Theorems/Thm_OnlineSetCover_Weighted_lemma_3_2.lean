-- Prove2me | Theorems.Thm_OnlineSetCover_Weighted_lemma_3_2
-- name    : OnlineSetCover.Weighted.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:44.494882+00:00
-- url     : https://prove2.me/theorems/673a521e-f7b8-4ea4-a9cf-c150697f4c2d
-- title:
--   Lemma 3.2 — the fractional cost $\sum_S w_S c_S$ stays at most $1 + (1+1/n)\,\alpha\log(m^2(1+1/n))$
-- statement:
--   Run the weighted online set-cover algorithm of Section 3 with guess $\alpha$ on an arrival sequence $\sigma$, with $n = |X|$ elements and $m = |\mathcal S|$ sets of costs $c_S$. Assume
--
--   1. $1 \le c_S \le m$ for every set $S$ (the normalization of p. 365);
--   2. a family $\mathcal C_{OPT} \subseteq \mathcal S$ covers every element of $\sigma$, with $c(\mathcal C_{OPT}) \le \alpha$.
--
--   Then at every configuration the algorithm reaches, with $N$ the number of weight augmentation steps performed so far,
--
--   $$\sum_{S \in \mathcal S} w_S c_S \le 1 + \frac{N}{n} \qquad\text{and hence}\qquad \sum_{S \in \mathcal S} w_S c_S \le 1 + \Big(1 + \frac1n\Big)\alpha \log\Big(m^2\Big(1 + \frac1n\Big)\Big).$$
--
--   The paper states the bound as $(2 + o(1))\alpha \log m$; the explicit expression is what its proof yields from the initial value $\sum_S w_S c_S \le 1$, the increase of at most $1/n$ per step, and Lemma 3.1.
--
--   This is the fractional-cost bound that Theorem 3.4 converts into a bound on the cost of the cover.
--
--   **Formalization Note** The first inequality holds at every intermediate configuration, including those inside an augmentation step, because $N$ counts a step as soon as it begins. The upper cost bound $c_S \le m$ is used only for the initial value.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 366, Lemma 3.2

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Weighted_Run

open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Weighted

/-- **Lemma 3.2** (Alon, Awerbuch, Azar, Buchbinder, Naor 2009, p. 366). Under the normalization
`1 ≤ c_S ≤ m` of p. 365, with `Copt` covering every arriving element and `c(Copt) ≤ α`: at every
running configuration reached by the algorithm, `∑_S w_S c_S ≤ 1 + N/n` (with `N` the number of
augmentation steps begun) and hence `∑_S w_S c_S ≤ 1 + (1 + 1/n) α log(m² (1 + 1/n))`, the
paper's `(2 + o(1)) α log m`. -/
theorem lemma_3_2 {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hc_m : ∀ S, inst.c S ≤ (Fintype.card T : ℝ))
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (s : AlgState X T) (hs : Reachable inst α σ (.ok s)) :
    ∑ S, s.w S * inst.c S ≤ 1 + (s.steps : ℝ) / (Fintype.card X : ℝ) ∧
      ∑ S, s.w S * inst.c S ≤
        1 + (1 + 1 / (Fintype.card X : ℝ)) * α *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) := by sorry

end OnlineSetCover.Weighted
