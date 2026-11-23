-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_Supplement_proposition_2
-- name    : MLRPCake.EnvyFree.Supplement.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:10:47.165088+00:00
-- url     : https://prove2.me/theorems/beae91d2-0639-403b-bdd1-79cccdaeafb0
-- title:
--   Proposition 2 — every moving-knife function MK_i is monotonically nondecreasing
-- statement:
--   For every cake-division instance $\mathcal C=\langle[n],\{f_i\}_i\rangle$ (no MLRP or Lipschitz assumption) and every $i\in[n]$, the moving-knife function
--   $$\mathrm{MK}_1(\tau)=\mathrm{Cut}_1(0,\tau),\qquad \mathrm{MK}_i(\tau)=\mathrm{Cut}_i(\mathrm{MK}_{i-1}(\tau),\tau)$$
--   is monotonically increasing in the weak sense: for all $0\le\tau\le\tau'$,
--   $$\mathrm{MK}_i(\tau)\le\mathrm{MK}_i(\tau').$$
--
--   It implies that feasibility of moving-knife targets is downward closed, which makes the binary search of Theorem 4 correct.
--
--   Differences from the source:
--   - reading: MK_i is monotonically increasing → τ ≤ τ′ ⇒ MK_i(τ) ≤ MK_i(τ′) for τ ≥ 0; reason: the proof shows the weak inequality, and MK_i is constant (= 1) for large τ, so strict increase is impossible
--   - encoding: MK_i for i ∈ [n] with MK_i : ℝ+ → [0,1] → mk f i for 1 ≤ i ≤ n, compared at τ ≥ 0; reason: mk f i is the paper's MK_i (agent i 0-based in Cut); same functions
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 21, Proposition 2

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_MovingKnife

namespace MLRPCake.EnvyFree.Supplement

/-- Proposition 2, p. 21: for every cake-division instance and every `i ∈ [n]`, the moving-knife
function `MK_i` is monotonically (weakly) increasing on `τ ≥ 0`. -/
theorem proposition_2 {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (i : ℕ) (hi1 : 1 ≤ i)
    (hin : i ≤ n) :
    ∀ τ τ' : ℝ, 0 ≤ τ → τ ≤ τ' → mk f i τ ≤ mk f i τ' := by sorry

end MLRPCake.EnvyFree.Supplement
