-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_no_fail_from_bounds
-- name    : KSATSingleFlip.Connect.repair_no_fail_from_bounds
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:48:24.046296+00:00
-- url     : https://prove2.me/theorems/b3bb3d57-9c6d-426f-b257-083ec27acdf1
-- title:
--   Repair cannot fail under small-set bounds
-- statement:
--   Consider a state $s$ reached by Repair on a finite formula $\Phi$ with nonempty clause scopes, starting from an assignment $x$ satisfying the designated subformula. Suppose $k\ge4$, local sparsity and the repair bounds hold, at most $\rho^4 n$ omitted clauses are weak under $x$, and $|U|\le\rho n$ for the state's current variable set $U$. If
--
--   $$2\left(\rho^4n+\max\!\left\{\rho^4n,\frac{|U|}{1024(\log k)^{20}}\right\}\right)\le\rho n,$$
--
--   then no next Repair step can return failure. This is the deterministic non-failure step in the proof of Lemma 7.12; bounding $|U|$ and obtaining the numerical inequality remain separate obligations.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf, proof of Lemma 7.12, printed p. 65 (PDF p. 67).

import Definitions.Def_KSATSingleFlip_Connect_Repair

namespace KSATSingleFlip.Connect

theorem repair_no_fail_from_bounds {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (c : Fin Φ.length)
    (hx : x ∈ sols (subF Φ I0))
    (hreach : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hk : 4 ≤ k) (hscope : ∀ c : Fin Φ.length, (vbl (Φ.get c)).Nonempty)
    (hLS : LS k Φ) (hBounds : RepairBounds k Φ I0 x)
    (hD : ((omittedWeak Φ I0 x).card : ℝ) ≤ rho k ^ 4 * n)
    (hU : (s.U.card : ℝ) ≤ rho k * n)
    (hnum : 2 * (rho k ^ 4 * n + max (rho k ^ 4 * n)
       (s.U.card / (1024 * Real.log k ^ 20))) ≤ rho k * n) :
    ¬ RStep k Φ I0 x s c none := by sorry

end KSATSingleFlip.Connect
