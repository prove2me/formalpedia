-- Prove2me | Theorems.Thm_MinSharing_lemma_2_1
-- name    : MinSharing.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:50.498804+00:00
-- url     : https://prove2.me/theorems/d0e16adb-37de-43ad-b90e-bd3d0e45b16c
-- title:
--   Lemma 2.1 — fPO iff non-malicious with no cycle of product $<1$ in $\overrightarrow{\mathcal{CG}}_z$
-- statement:
--   Let $v$ be an $n\times m$ valuation matrix with entries of any sign and let $z$ be an allocation. Then $z$ is fractionally Pareto-optimal if and only if
--
--   1. $z$ is non-malicious (goods are consumed only by agents valuing them positively, neutral objects only by agents valuing them at $0$), and
--   2. the weighted directed consumption graph $\overrightarrow{\mathcal{CG}}_z$ has no cycle $C$ with
--   $$\pi(C)<1 .$$
--
--   This is the dual description of efficiency used throughout the paper: an inefficient allocation is one that admits a profitable cyclic trade, and it underlies the fPO test of Lemma 2.2 and the cycle-cancelling construction of Lemma 2.5.
--
--   Differences from the source:
--   - encoding: z is an allocation → hypothesis IsFeasible z (z ≥ 0, every column sums to 1); reason: the definition of an allocation on p.7
--   - encoding: cycle C = (i₁ → o₁ → … → o_L → i_{L+1} = i₁) → closed walk with L ≥ 1 in which agents and objects may repeat; reason: a closed walk with product < 1 contains a simple cycle with product < 1 (the weights are nonnegative), so the condition is the same
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Lemma 2.1, p.9 (proof Appendix A, pp.29–30)

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_MinSharing_Setting
import Definitions.Def_MinSharing_DirectedConsumptionGraph

set_option autoImplicit false

namespace MinSharing

open CompetitiveChores.RichFamily

/-- **Lemma 2.1** (Sandomirskiy, Segal-Halevi, arXiv:1908.01669v3, p.9; proof Appendix A,
pp.29–30). An allocation `z` is fractionally Pareto-optimal if and only if it is non-malicious
and its directed consumption graph `→CG_z` has no cycle `C` with `π(C) < 1`.

**Formalization Note** Agents `Fin n`, objects `Fin m`, values `v` of any sign. "An allocation"
is the hypothesis `IsFeasible z` (`z ≥ 0`, column sums `1`). A cycle is a closed walk
`a 0 → b 0 → a 1 → … → b (L−1) → a L = a 0` with `L ≥ 1` (`IsDirectedCycle`), and `π(C)` is
`cycleProduct`. -/
theorem lemma_2_1 {n m : ℕ} (v z : Fin n → Fin m → ℝ) (hz : IsFeasible z) :
    IsParetoOptimal v z ↔
      IsNonMalicious v z ∧
        ∀ (L : ℕ) (a : Fin (L + 1) → Fin n) (b : Fin L → Fin m),
          IsDirectedCycle v z L a b → 1 ≤ cycleProduct v L a b := by sorry

end MinSharing
