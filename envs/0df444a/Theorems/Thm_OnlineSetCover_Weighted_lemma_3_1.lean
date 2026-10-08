-- Prove2me | Theorems.Thm_OnlineSetCover_Weighted_lemma_3_1
-- name    : OnlineSetCover.Weighted.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:51.166215+00:00
-- url     : https://prove2.me/theorems/dbe53511-b1aa-4e73-b217-227fa53dc1bb
-- title:
--   Lemma 3.1 — the number of weight augmentation steps is at most $(n+1)\,\alpha\log(m^2(1+1/n))$
-- statement:
--   Run the weighted online set-cover algorithm of Section 3 with guess $\alpha$ on an arrival sequence $\sigma$ of elements of the ground set $X$ ($n = |X|$) over a family $\mathcal S$ of $m$ sets with costs $c_S$. Assume
--
--   1. every set costs at least $1$ (the normalization of p. 365);
--   2. a family $\mathcal C_{OPT} \subseteq \mathcal S$ covers every element of $\sigma$;
--   3. $c(\mathcal C_{OPT}) = \sum_{S \in \mathcal C_{OPT}} c_S \le \alpha$ (for the second inequality only).
--
--   Then at every configuration the algorithm reaches, the number $N$ of weight augmentation steps performed so far satisfies
--
--   $$N \le \sum_{S \in \mathcal C_{OPT}} (n c_S + 1) \log\Big(m^2\Big(1 + \frac1n\Big)\Big) \le (n+1)\,\alpha \log\Big(m^2\Big(1 + \frac1n\Big)\Big).$$
--
--   The logarithm is natural. The paper writes the right-hand side as $(2 + o(1)) n \alpha \log m$; the explicit bound $(n+1)\alpha\log(m^2(1+1/n))$ is what its proof gives, using $|\mathcal C_{OPT}| \le c(\mathcal C_{OPT}) \le \alpha$ since every cost is at least $1$.
--
--   This count is the input to Lemma 3.2, which turns it into a bound on the fractional cost $\sum_S w_S c_S$.
--
--   **Formalization Note** $N$ counts the augmentation steps that have begun, including one in progress. The bound holds for every visiting order of $\mathcal S_j$ and does not depend on which sets the algorithm has added to the cover.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 365, Lemma 3.1 (proof p. 366)

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Weighted_Run

open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Weighted

/-- **Lemma 3.1** (Alon, Awerbuch, Azar, Buchbinder, Naor 2009, p. 365). Let every set cost at
least `1` (the normalization of p. 365) and let `Copt` cover every arriving element. At every
running configuration reached by the algorithm with guess `α` on `σ`, the number of weight
augmentation steps begun is at most `∑_{S ∈ Copt} (n c_S + 1) log(m² (1 + 1/n))`, and when
`c(Copt) ≤ α` this is at most `(n + 1) α log(m² (1 + 1/n))` (the paper's `(2 + o(1)) n α log m`).
Here `n = |X|`, `m = |T|`, natural logarithm. -/
theorem lemma_3_1 {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (s : AlgState X T) (hs : Reachable inst α σ (.ok s)) :
    (s.steps : ℝ) ≤
        ∑ S ∈ Copt, ((Fintype.card X : ℝ) * inst.c S + 1) *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) ∧
      ∑ S ∈ Copt, ((Fintype.card X : ℝ) * inst.c S + 1) *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) ≤
        ((Fintype.card X : ℝ) + 1) * α *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) := by sorry

end OnlineSetCover.Weighted
