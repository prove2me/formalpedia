-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_success_output
-- name    : KSATSingleFlip.Connect.repair_success_output
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:22:08.619181+00:00
-- url     : https://prove2.me/theorems/e06af817-81d8-4857-82ea-3627b5104df9
-- title:
--   A successful Repair output satisfies the formula and has the required support
-- statement:
--   Let $\Phi$ be a finite Boolean formula, $I_0$ a set of clause positions, $x$ an assignment, $W$ a set of variables, and $k$ a natural number. If a completed run of Algorithm 3 returns $(U,y)$, then
--
--   $$W\subseteq U,\qquad y\models\Phi,\qquad y(v)=x(v)\quad\text{for every }v\notin U.$$
--
--   This is a supporting correctness property for the repair algorithm. It applies to every successful run, but does not assert that a run succeeds or establish its shortest-path property.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://arxiv.org/abs/2611.05981, Algorithm 3 and proof of Lemma 7.4, pp. 60–62; derived supporting statement.

import Definitions.Def_KSATSingleFlip_Connect_Repair

namespace KSATSingleFlip.Connect

/-- A successful Repair run returns a satisfying assignment with the required support. -/
theorem repair_success_output {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ)
    (hrun : RepairRun k Φ I0 x (RState.init Φ x W) r i) :
    ∀ U y, r = some (U, y) →
      W ⊆ U ∧ y ∈ sols Φ ∧ ∀ u, u ∉ U → y u = x u := by sorry

end KSATSingleFlip.Connect
