-- Prove2me | Theorems.Thm_FullForesight_Randomized_lemma_2
-- name    : FullForesight.Randomized.lemma_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:17:08.035358+00:00
-- url     : https://prove2.me/theorems/da384469-151a-4f55-b547-b3caba4988d5
-- title:
--   Lemma 2 — an interval-selection bound gives $\alpha$-addition-robust distributions
-- statement:
--   Let $\alpha \in [0, 1]$. Suppose that $\Gamma(\ell, r, p) \ge \alpha$ for every interval-selection instance $(\ell, r, p)$. Then every instance of clairvoyant addition-robust submodular maximization — a nonnegative monotone submodular $f$, present elements $V_{\mathrm{now}}$, distinct future elements $v_1, \dots, v_m \notin V_{\mathrm{now}}$, any budget $\kappa$ — admits an $\alpha$-addition-robust distribution: a probability distribution $\mu$ on the subsets of $V_{\mathrm{now}}$, supported on sets of size at most $\kappa$, with
--   $$\mathbb E_{S \sim \mu}[f(S \cup R_j)] \ge \alpha \max_{O \subseteq V_{\mathrm{now}},\, |O| \le \kappa} f(O \cup R_j) \qquad (j = 0, \dots, m).$$
--
--   This connects the geometric interval-selection problem to the addition-robust problem of §2.3.
--
--   Differences from the source:
--   - encoding: instances on an abstract ground set → a ground type `X` with decidable equality, $f$ defined on all of `Finset X`; reason: a function on $V_{\mathrm{now}} \cup \{v_1, \dots, v_m\}$ extends by $S \mapsto f(S \cap G)$ with the same values on the ground set, and every ground set is such a type.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 9, Lemma 2 (restated and proved p. 24)

import Mathlib
import Definitions.Def_FullForesight_Randomized_IntervalSelection
import Definitions.Def_FullForesight_Randomized_AdditionRobust

namespace FullForesight.Randomized

theorem lemma_2 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ (N : ℕ) (ℓ r p : Fin (N + 1) → ℝ), IsIntervalInstance ℓ r p → α ≤ gap ℓ r p) :
    ∀ (X : Type) [DecidableEq X] (m : ℕ) (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X)
      (κ : ℕ), IsARInstance f Vnow v → ∃ μ : Finset X → ℝ, IsRobustDist f Vnow v κ α μ := by sorry

end FullForesight.Randomized
