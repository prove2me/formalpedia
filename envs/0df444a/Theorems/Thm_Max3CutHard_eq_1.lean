-- Prove2me | Theorems.Thm_Max3CutHard_eq_1
-- name    : Max3CutHard.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:49.531091+00:00
-- url     : https://prove2.me/theorems/f3e1c966-7ab0-4b87-8b0e-188886bdac01
-- title:
--   Eq. (1) — completeness of the gadget reduction
-- statement:
--   Let $k\ge3$, let $(I_0,I_1,I_2)$ be a family of gadgets with non-negative weights, and let $\Phi$ be a balanced role-separated instance on finite variable sets with weights $\lambda_e\ge0$ summing to $1$. If $\mathrm{val}(\Phi)\ge1-\varepsilon$, then
--
--   $$\max_\chi\mathrm{cut}_\chi(J(\Phi))\ \ge\ \frac13\sum_{t}C_t-\varepsilon\max_tC_t,$$
--
--   where $C_t$ is the completeness of $I_t$. (In the source, the colouring giving this bound colours the variables by an assignment satisfying weight at least $1-\varepsilon$, the globals by $y^\circ$, and the auxiliary vertices of each satisfied equation optimally.)
--
--   Differences from the source:
--   - generalization: ε > 0 (the ε of Theorem 2.1) → every real ε; reason: the source's ε > 0 is the special case; ε = 0 is included, and for ε < 0 the hypothesis on val(Φ) cannot hold (1/3 ≤ val(Φ) ≤ 1 for every weighted role-separated instance)
--   - encoding: k ≥ 3 → 3 ≤ k together with the instance NeZero k; reason: NeZero k is implied by 3 ≤ k and is needed to form the maxima
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, The reduction, Eq. (1), p.5

import Mathlib
import Definitions.Def_Max3CutHard_J
import Definitions.Def_Max3CutHard_maxCutR
import Definitions.Def_Max3CutHard_Ct
import Definitions.Def_Max3CutHard_IsNonneg
import Definitions.Def_Max3CutHard_WInst_IsWeighting
import Definitions.Def_Max3CutHard_WInst_Balanced
import Definitions.Def_Max3CutHard_WInst_val

namespace Max3CutHard

/-- **Eq. (1): completeness of the reduction.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, The reduction, Eq. (1), p.5: "If
`val(Φ) ≥ 1 − ε` and `Φ` is balanced, colouring the variables by an assignment that satisfies
weight at least `1 − ε`, the globals by `y°`, and the auxiliary vertices of each satisfied
equation optimally gives `max_χ cut_χ(J) ≥ (1/3) Σ_t C_t − ε max_t C_t`. (1)"

**Formalization Note.** Every `k ≥ 3` (`NeZero k` is the instance form of `k ≠ 0`, implied by
`3 ≤ k`), every family of non-negatively weighted gadgets, every balanced weighted instance and
every real `ε`. `max_t C_t` is a `Finset.sup'` over `ℤ₃`. -/
theorem eq_1 {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (F : Family k) (hF : ∀ t, IsNonneg (F t).edges)
    (Φ : WInst U W) (hΦ : Φ.IsWeighting) (hbal : Φ.Balanced) (ε : ℝ) (hval : 1 - ε ≤ Φ.val) :
    (1 / 3) * ∑ t : ZMod 3, Ct hk F t - ε * Finset.univ.sup' Finset.univ_nonempty (Ct hk F)
      ≤ maxCutR k (J Φ F) := by sorry

end Max3CutHard
