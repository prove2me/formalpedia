-- Prove2me | Theorems.Thm_OnlineSetCover_Weighted_theorem_3_4
-- name    : OnlineSetCover.Weighted.theorem_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:53.085025+00:00
-- url     : https://prove2.me/theorems/2ede1f24-a9ba-4202-9570-253d34304747
-- title:
--   Theorem 3.4 — given $\alpha \ge c(\mathcal C_{OPT})$, the algorithm never fails, covers every element of weight $\ge 1$, and pays $(6+o(1))\,\alpha\log m\log n$
-- statement:
--   Consider weighted online set cover on a ground set $X$ with $n = |X|$ elements and a family $\mathcal S$ of $m$ sets with costs $c_S$, and run the deterministic algorithm of Section 3 with guess $\alpha$ on an arrival sequence $\sigma$. Assume the normalized instance of p. 365:
--
--   1. $1 \le c_S \le m$ and $c_S \le \alpha$ for every set $S$;
--   2. a family $\mathcal C_{OPT} \subseteq \mathcal S$ covers every element of $\sigma$, and $c(\mathcal C_{OPT}) \le \alpha$;
--   3. $n$ and $m$ are large enough that $n \cdot n^{2/m} + n < n^2$ (for instance $n \ge 4$ and $m \ge 3$).
--
--   Then every configuration the algorithm reaches is a running state, never FAIL, and in it
--
--   (i) every element $j \in X$ of weight $w_j \ge 1$ is covered by the current cover $\mathcal C$;
--
--   (ii) the cost of the current cover satisfies
--   $$\sum_{S \in \mathcal C} c_S \le 3 \log n \Big(1 + \Big(1 + \frac1n\Big)\alpha \log\Big(m^2\Big(1+\frac1n\Big)\Big)\Big) + 2\alpha \log n.$$
--
--   The logarithm is natural. The paper writes (ii) as $\sum_{S \in \mathcal C} c_S \le (6 + o(1))\alpha \log m \log n$ with $o(1) \to 0$ as $n, m \to \infty$; the displayed expression is what its proof yields from Lemma 3.2 and is $(6 + o(1))\alpha \log m \log n$ because $\alpha \ge 1$.
--
--   Together with the doubling over guesses of $\alpha$ (not part of this statement), this gives the paper's deterministic $O(\log m \log n)$-competitive algorithm for weighted online set cover.
--
--   **Formalization Note** "Throughout the algorithm" is every configuration reachable from the initial state ($w_S = 1/m^2$, empty cover), including those between the per-set substeps of an augmentation step, for every order in which a step visits $\mathcal S_j$. Part (i) is asserted for every element of $X$, not only for arrived ones. The size condition is the inequality the proof uses for the initial potential; the paper only says that $n$ and $m$ are large.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 367, Theorem 3.4 (standing assumptions p. 365)

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Weighted_Run

open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Weighted

/-- **Theorem 3.4** (Alon, Awerbuch, Azar, Buchbinder, Naor 2009, p. 367). On the normalized
instance of p. 365 (`1 ≤ c_S ≤ m` and `c_S ≤ α` for every set), with `Copt` covering every
arriving element and `c(Copt) ≤ α`, and with `n, m` large in the sense the proof uses
(`n · n^(2/m) + n < n²`): every configuration the algorithm reaches on `σ` is a running state
(never `FAIL`) in which
(i) every element `j ∈ X` with `w_j ≥ 1` is covered, and
(ii) `∑_{S ∈ C} c_S ≤ 3 log n (1 + (1 + 1/n) α log(m² (1 + 1/n))) + 2 α log n`,
the explicit form of the paper's `(6 + o(1)) α log m log n`. -/
theorem theorem_3_4 {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hc_m : ∀ S, inst.c S ≤ (Fintype.card T : ℝ))
    (hc_α : ∀ S, inst.c S ≤ α)
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (hsize : (Fintype.card X : ℝ) * (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) +
        (Fintype.card X : ℝ) < (Fintype.card X : ℝ) ^ 2)
    (c : Config X T) (hc : Reachable inst α σ c) :
    ∃ s : AlgState X T, c = .ok s ∧
      (∀ j : X, 1 ≤ elementWeight inst s.w j → coveredBy inst s.C j) ∧
      ∑ S ∈ s.C, inst.c S ≤
        3 * Real.log (Fintype.card X : ℝ) *
            (1 + (1 + 1 / (Fintype.card X : ℝ)) * α *
              Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ)))) +
          2 * α * Real.log (Fintype.card X : ℝ) := by sorry

end OnlineSetCover.Weighted
