-- Prove2me | Theorems.Thm_FullForesight_Randomized_lemma_1
-- name    : FullForesight.Randomized.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:17:08.279644+00:00
-- url     : https://prove2.me/theorems/56cf325b-3b2c-4efe-88d9-0b02b3ddffd8
-- title:
--   Lemma 1 — the checkpoint reduction: addition-robust distributions give $O(\gamma^{-2})$-consistent $(\alpha - 3\gamma)$-approximations
-- statement:
--   There is a universal constant $c$ with the following property. Let $0 \le \alpha \le 1$ and $\gamma \in (0, 1/8)$, and suppose that every instance of the clairvoyant addition-robust problem (any ground set, any nonnegative monotone submodular $f$, any $V_{\mathrm{now}}$, any distinct future elements outside $V_{\mathrm{now}}$, any budget $\kappa$) admits an $\alpha$-addition-robust distribution. Then for every instance of clairvoyant monotone submodular maximization ($n$ arrivals, $k \ge 1$, $f \ge 0$ monotone submodular) there is a valid law of solution trajectories that is $c\gamma^{-2}$-consistent on every realization and satisfies
--   $$\mathbb E[f(\mathrm{ALG}_t)] \ge (\alpha - 3\gamma)\, f(\mathrm{OPT}_t) \qquad (t = 0, \dots, n).$$
--
--   This reduces the consistent problem to the static addition-robust problem.
--
--   Differences from the source:
--   - encoding: "an algorithm returns an α-addition-robust distribution for every instance" → every instance admits one; reason: computation is unrestricted, so an algorithm returning one exists exactly when one exists for each instance.
--   - encoding: "this yields a randomized clairvoyant $O(\gamma^{-2})$-consistent algorithm" → a universal $c$, chosen before $\alpha$, $\gamma$ and the instance, and for every instance a valid $c\gamma^{-2}$-consistent law of trajectories; reason: a clairvoyant algorithm with unrestricted computation is a per-instance law of trajectories (Model), and $O(\cdot)$ is an absolute constant.
--   - encoding: ground set of the arrivals → `Fin n` in arrival order, approximation required also at $t = 0$; reason: arrivals are distinct, so they relabel to `Fin n`; at $t = 0$ both sides are $f(\emptyset)$ times a factor $\le 1$, so that time adds no constraint.
--   - encoding: addition-robust instances in the hypothesis → a ground type `X` with decidable equality, $f$ defined on all of `Finset X`; reason: only sets inside $V_{\mathrm{now}} \cup \{v_1, \dots, v_m\}$ are evaluated, so an $\alpha$-addition-robust distribution for the restriction of $f$ to that ground set is one for $f$; the hypothesis is equivalent to the paper's.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 7, Lemma 1 (restated and proved pp. 22–23)

import Mathlib
import Definitions.Def_FullForesight_Randomized_Model
import Definitions.Def_FullForesight_Randomized_AdditionRobust

namespace FullForesight.Randomized

theorem lemma_1 :
    ∃ c : ℝ, ∀ α γ : ℝ, 0 ≤ α → α ≤ 1 → γ ∈ Set.Ioo (0 : ℝ) (1 / 8) →
      (∀ (X : Type) [DecidableEq X] (m : ℕ) (f : Finset X → ℝ) (Vnow : Finset X)
        (v : Fin m → X) (κ : ℕ), IsARInstance f Vnow v →
          ∃ μ : Finset X → ℝ, IsRobustDist f Vnow v κ α μ) →
      ∀ (n k : ℕ) (f : Finset (Fin n) → ℝ), IsInstance k f →
        ∃ L : TrajLaw n, L.Valid k ∧ L.Consistent (c / γ ^ 2) ∧ L.Approx f k (α - 3 * γ) := by sorry

end FullForesight.Randomized
