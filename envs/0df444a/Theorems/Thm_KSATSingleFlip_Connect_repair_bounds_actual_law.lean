-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_bounds_actual_law
-- name    : KSATSingleFlip.Connect.repair_bounds_actual_law
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T05:21:18.263742+00:00
-- url     : https://prove2.me/theorems/652ddd81-7b17-4009-9837-b00f616167fc
-- title:
--   Repair bounds under the fixed-start Glauber law
-- statement:
--   For all sufficiently large $k$ and then sufficiently large $n$, let $m$ be nonnegative and in the density range of Lemma 7.11, and fix an initial assignment $z$ and a time $t$. Draw a Poisson random $k$-SAT formula $\Phi^+$ with mean $m$, retain the clause occurrences satisfied by $z$ as $\Phi_0$, and run $t$ Glauber steps on $\Phi_0$ from $z$, obtaining $X$. Then
--
--   $$\Pr[\operatorname{RepairBounds}(k,\Phi^+,\Phi_0,X)]\ge1-e^{-\rho(k)^8 n}.$$
--
--   The estimate is uniform in $z$ and $t$, with original clause positions retained. This isolates the planted-law and Poisson-thinning transport used after Lemma 7.12 in the proof of Lemma 7.4.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf, proof of Lemma 7.4 immediately after Lemma 7.12, printed p. 65 (PDF p. 67).

import Definitions.Def_KSATSingleFlip_Connect_Repair
import Definitions.Def_KSATSingleFlip_Connect_Glauber

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.11's small-set bounds transported to the actual fixed-start
Poisson formula and planted-subformula Glauber law used in Lemma 7.4. -/
theorem repair_bounds_actual_law :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      m ≤ (2 : ℝ) ^ k * n / k * loosenessLambda k →
      ∀ (z : Fin n → Bool) (t : ℕ),
        1 - Real.exp (-(rho k ^ 8) * n) ≤
          poisExp (allClauses n k) m (fun l =>
            uprob fun s : Fin t → Fin n × Bool =>
              let Φ := ofList l
              let I0 := satIdx Φ z
              let X := glauberState (subF Φ I0) z s
              RepairBounds k Φ I0 X) := by
  sorry

end KSATSingleFlip.Connect
