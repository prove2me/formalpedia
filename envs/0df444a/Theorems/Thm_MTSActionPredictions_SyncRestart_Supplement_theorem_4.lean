-- Prove2me | Theorems.Thm_MTSActionPredictions_SyncRestart_Supplement_theorem_4
-- name    : MTSActionPredictions.SyncRestart.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:28:45.32097+00:00
-- url     : https://prove2.me/theorems/4529ca6f-e25c-4591-b1c4-e86597e0e103
-- title:
--   Theorem 4 — Euclidean convex body chasing with action predictions: strict ratio $O(\min\{d,\sqrt{1+\eta/\mathrm{OFF}}\})$
-- statement:
--   There is a universal constant $C>0$ with the following property. For every dimension $d$ and every start point $x_0\in\mathbb R^d$ there is a deterministic online algorithm for Euclidean convex body chasing with action predictions such that, for every input $(K_1,P_1),\dots,(K_T,P_T)$ of nonempty closed convex sets $K_t\subseteq\mathbb R^d$ and arbitrary predicted points $P_t\in\mathbb R^d$, and for every feasible offline solution $y$ from $x_0$ with cost $\mathrm{OFF}$ and prediction error $\eta=\sum_t\|P_t-y_t\|$,
--   $$\mathrm{ALG}\le C\cdot\min\Big\{d\cdot\mathrm{OFF},\ \sqrt{\mathrm{OFF}\,(\mathrm{OFF}+\eta)}\Big\}.$$
--   That is, the algorithm has strict competitive ratio $O\big(\min\{d,\sqrt{1+\eta/\mathrm{OFF}}\}\big)$ against every offline solution, with no additive constant.
--
--   The square-root dependence on the normalized error is asymptotically optimal (Lemma 36 of the paper), while the term $d$ is the fallback without predictions.
--
--   Differences from the source:
--   - reading: strict competitive ratio O(min{d, √(1+η/OFF)}) against OFF → a universal C > 0 with ALG ≤ C·min{d·OFF, √(OFF(OFF+η))}; reason: multiplying the ratio by OFF; the d·OFF branch gives the strict bound ALG = 0 when OFF = 0, where η/OFF is undefined
--   - reading: there exists an algorithm (randomization does not help, PDF 23) → there exists a deterministic online algorithm, which may depend on d and x₀; reason: the source states that every randomized algorithm can be derandomized by following its expected position; the deterministic reading is the stronger one
--   - encoding: requests K_t and predictions P_t revealed together → a list of (set, point) pairs; feasibility x_t ∈ K_t required along sequences of bodies; real-valued costs; reason: same instances; all costs are finite sums of norms
--   - encoding: R^d with d ≥ 1 → every d : ℕ, including d = 0; reason: R^0 is a single point, where every cost is 0 and the bound holds trivially; no instance with d ≥ 1 changes
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; Theorem 4, PDF p. 4 / printed p. 3, restated PDF p. 23 / printed p. 22; proof PDF p. 25 / printed p. 24

import Definitions.Def_MTSActionPredictions_SyncRestart_Supplement_ConvexChasing

open CBCLowerBound.EveryNorm

namespace MTSActionPredictions.SyncRestart.Supplement

/-- Theorem 4, PDF 4 and 23 / printed 3 and 22: there is a universal constant `C` such that in
every dimension `d` and from every start `x₀` some deterministic online algorithm for Euclidean
convex body chasing with action predictions satisfies, on every input and against every feasible
offline solution `y` (with `OFF` its cost and `η` its prediction error),
`ALG ≤ C · min {d · OFF, √(OFF · (OFF + η))}`, i.e. strict competitive ratio
`O(min {d, √(1 + η/OFF)})` against `OFF`. -/
theorem theorem_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (x₀ : EuclideanSpace ℝ (Fin d)),
      ∃ A : PredAlgorithm (EuclideanSpace ℝ (Fin d)) x₀,
        ∀ σ : List (Set (EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d)),
          (∀ a ∈ σ, IsBody a.1) →
          ∀ y : ℕ → EuclideanSpace ℝ (Fin d), FeasiblePath x₀ (σ.map Prod.fst) y →
            A.cost σ ≤ C * min ((d : ℝ) * pathCost σ.length y)
              (Real.sqrt (pathCost σ.length y * (pathCost σ.length y + predError σ y))) := by sorry

end MTSActionPredictions.SyncRestart.Supplement
