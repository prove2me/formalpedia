-- Prove2me | Theorems.Thm_LowRankIndicator_feas7_isBounded
-- name    : LowRankIndicator.feas7_isBounded
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:44.457012+00:00
-- url     : https://prove2.me/theorems/72d1540c-35bc-4fc7-a53a-1d6bfbf66f00
-- title:
--   Proof of Theorem 1, p.8 — if the cone $\{x:Ax=0,\ x_i\ge0\ \forall i\in I_+\}$ is $\{0\}$, the feasible region of (7) is bounded
-- statement:
--   Suppose that
--
--   $$\{x\in\mathbb R^n:Ax=0,\ x_i\ge0\ \forall i\in I_+\}=\{0\}.$$
--
--   Then for every $(\bar t,\bar x,\bar z)\in Q$ the feasible region of the linear program (7) is a bounded subset of $\mathbb R^n$.
--
--   This is the reason why $R$ can be dropped from the main theorem under the cone hypothesis: the value of (7) is then always finite.
--
--   Differences from the source:
--   - generalization: g proper closed convex → arbitrary g : ℝᵏ → `EReal`; reason: the statement holds without these properties and specializes to the paper's g
--   - encoding: bounded → `Bornology.IsBounded` in `Fin n → ℝ`; reason: all norms on ℝⁿ give the same bounded sets
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, proof of Theorem 1, p.8, "The last statement of the theorem follows".

import Mathlib
import Definitions.Def_LowRankIndicator_Sets
import Definitions.Def_LowRankIndicator_FeasibleSet7

namespace LowRankIndicator

/-- Han & Gómez, arXiv:2110.14884v2, proof of Theorem 1, p.8: "if {x ∈ Rn : Ax = 0, xi ≥ 0 ∀i ∈
I+} = {0}, then the feasible region of (7) is bounded", for every `(t̄, x̄, z̄) ∈ Q`.

**Formalization Note.** Membership in `Q` supplies `x̄ᵢ ≥ 0` on `I₊`, which puts the directions of
(7) into the cone. Boundedness is `Bornology.IsBounded` in `Fin n → ℝ`. -/
theorem feas7_isBounded {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin n → ℝ) (Iplus : Set (Fin n)) {tbar : ℝ} {xbar zbar : Fin n → ℝ}
    (hcone : recCone A Iplus = {0}) (hbar : (tbar, xbar, zbar) ∈ Q g A c Iplus) :
    Bornology.IsBounded (feas7 A xbar) := by sorry

end LowRankIndicator
