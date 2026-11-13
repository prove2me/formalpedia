-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_no_fail
-- name    : KSATSingleFlip.Connect.repair_no_fail
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:50:26.172693+00:00
-- url     : https://prove2.me/theorems/071eea48-b022-4c0d-aabe-85d7bb8b6dfe
-- title:
--   Repair cannot fail while its repair set is small
-- statement:
--   Consider a state reached by Repair on a finite formula $\Phi$ with nonempty clause scopes, starting from an assignment $x$ satisfying the designated subformula. Suppose $k\ge4$, $\log k\ge1$, local sparsity and the repair bounds hold, at most $\rho^4n$ omitted clauses are weak under $x$, and the current variable set satisfies $|U|\le\rho n$. Then no next Repair step returns failure.
--
--   This isolates the non-failure part of the proof of Lemma 7.12. Establishing the size bound for every reached state is a separate obligation.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf, proof of Lemma 7.12, printed p. 65 (PDF p. 67).

import Definitions.Def_KSATSingleFlip_Connect_Repair

namespace KSATSingleFlip.Connect

/-- Repair cannot fail while its repair set is small under local sparsity and the source bounds. -/
theorem repair_no_fail {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (c : Fin Φ.length)
    (hx : x ∈ sols (subF Φ I0))
    (hreach : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hk : 4 ≤ k) (hlog : 1 ≤ Real.log k)
    (hscope : ∀ c : Fin Φ.length, (vbl (Φ.get c)).Nonempty)
    (hLS : LS k Φ) (hBounds : RepairBounds k Φ I0 x)
    (hD : ((omittedWeak Φ I0 x).card : ℝ) ≤ rho k ^ 4 * n)
    (hU : (s.U.card : ℝ) ≤ rho k * n) :
    ¬ RStep k Φ I0 x s c none := by sorry

end KSATSingleFlip.Connect
