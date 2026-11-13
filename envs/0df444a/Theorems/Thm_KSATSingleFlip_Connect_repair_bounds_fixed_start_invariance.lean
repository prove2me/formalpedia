-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_bounds_fixed_start_invariance
-- name    : KSATSingleFlip.Connect.repair_bounds_fixed_start_invariance
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:45:15.659482+00:00
-- url     : https://prove2.me/theorems/187420e4-6ff3-4cc5-a071-e4fa0c76038f
-- title:
--   Fixed-start symmetry of the repair-bounds event
-- statement:
--   The probability that the three repair bounds hold for the Poisson formula and Glauber chain is the same for every fixed starting assignment. Choose a Poisson random k-SAT formula, retain the clause occurrences satisfied by the start, and run t uniform Glauber updates on the retained formula; the equality holds for all n, k, m and t.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, proof of probabilistic Lemma 7.4 after Lemma 7.12, printed p. 65 (PDF p. 67), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Repair
import Definitions.Def_KSATSingleFlip_Connect_Glauber

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- The small-set-bounds probability under the actual law is independent of the fixed start. -/
theorem repair_bounds_fixed_start_invariance {n : ℕ} (k : ℕ) (m : ℝ)
    (z z' : Fin n → Bool) (t : ℕ) :
    poisExp (allClauses n k) m (fun l => uprob fun s : Fin t → Fin n × Bool =>
      let Φ := ofList l
      let I0 := satIdx Φ z
      let X := glauberState (subF Φ I0) z s
      RepairBounds k Φ I0 X) =
    poisExp (allClauses n k) m (fun l => uprob fun s : Fin t → Fin n × Bool =>
      let Φ := ofList l
      let I0 := satIdx Φ z'
      let X := glauberState (subF Φ I0) z' s
      RepairBounds k Φ I0 X) := by sorry

end KSATSingleFlip.Connect
