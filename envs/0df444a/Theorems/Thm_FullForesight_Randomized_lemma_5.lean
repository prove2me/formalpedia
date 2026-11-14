-- Prove2me | Theorems.Thm_FullForesight_Randomized_lemma_5
-- name    : FullForesight.Randomized.lemma_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:17:05.314657+00:00
-- url     : https://prove2.me/theorems/1ef249b1-6d79-41ce-8f79-86c73b0b6718
-- title:
--   Lemma 5 — minimax duality for the addition-robustness LP (1)
-- statement:
--   Let $(f, V_{\mathrm{now}}, v_1, \dots, v_m)$ be an instance of the clairvoyant addition-robust problem with budget $\kappa \ge 1$ ($f \ge 0$ monotone submodular, future elements distinct and not present), let $O_0, \dots, O_m$ be any family of prefix optimizers, and assume $f(O_0) > 0$. Let $\rho^\star$ be the value of LP (1) for these optimizers and $w_{i,j} = f(O_i \cup R_j)/f(O_j \cup R_j)$. Then
--   $$\rho^\star = \max_{\alpha \in \Delta}\ \min_{j = 0, \dots, m}\ \sum_{i=0}^m \alpha_i w_{i,j} = \min_{\beta \in \Delta}\ \max_{i = 0, \dots, m}\ \sum_{j=0}^m \beta_j w_{i,j},$$
--   where $\Delta$ is the simplex of probability vectors on $\{0, \dots, m\}$, and the outer maximum and minimum are attained.
--
--   This turns the search for one robust random solution into a game where the adversary first commits to a distribution over prefixes; Lemma 2 uses the second form.
--
--   Differences from the source:
--   - reading: "$\rho^\star = \max_\alpha \min_j \dots = \min_\beta \max_i \dots$" → $\rho^\star$ is the greatest element of $\{\min_j \sum_i \alpha_i w_{i,j} : \alpha \in \Delta\}$ and the least element of $\{\max_i \sum_j \beta_j w_{i,j} : \beta \in \Delta\}$; reason: "max" and "min" assert attainment, which is stated rather than replaced by sup and inf.
--   - reading: "$O_j \in \arg\max$" (one choice of maximizers) → the statement holds for every family of prefix optimizers; reason: the paper fixes an arbitrary choice; quantifying over all choices states it for each.
--   - encoding: "the value of the linear program (1)" → `lpValue`, the supremum of the feasible $\rho \in [0, 1]$; reason: under the hypotheses the feasible set contains $\rho = 0$ and is bounded by $1$, and LP (1) attains its optimum (compact feasible region), so the supremum is the LP's value.
--   - encoding: instances on an abstract ground set → a ground type `X` with decidable equality, $f$ defined on all of `Finset X`; reason: only sets inside $V_{\mathrm{now}} \cup \{v_1, \dots, v_m\}$ are ever evaluated, a function on that ground set $G$ extends by $S \mapsto f(S \cap G)$ with the same values, and every ground set is such a type.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 23, Lemma 5 (LP (1) on p. 8)

import Mathlib
import Definitions.Def_FullForesight_Randomized_AdditionRobust

namespace FullForesight.Randomized

theorem lemma_5 {X : Type} [DecidableEq X] {m : ℕ} (f : Finset X → ℝ) (Vnow : Finset X)
    (v : Fin m → X) (κ : ℕ) (O : Fin (m + 1) → Finset X)
    (hinst : IsARInstance f Vnow v) (hO : IsMaximizerFamily f Vnow v κ O)
    (hκ : 1 ≤ κ) (hpos : 0 < f (O 0)) :
    IsGreatest {x : ℝ | ∃ a ∈ stdSimplex ℝ (Fin (m + 1)),
        x = Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, a i * payoff f v O i j)}
        (lpValue f v O) ∧
      IsLeast {x : ℝ | ∃ b ∈ stdSimplex ℝ (Fin (m + 1)),
        x = Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, b j * payoff f v O i j)}
        (lpValue f v O) := by sorry

end FullForesight.Randomized
