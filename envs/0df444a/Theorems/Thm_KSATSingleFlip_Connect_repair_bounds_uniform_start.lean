-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_bounds_uniform_start
-- name    : KSATSingleFlip.Connect.repair_bounds_uniform_start
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T05:45:23.280534+00:00
-- url     : https://prove2.me/theorems/7408e1f7-c974-462c-b70c-4f0700f8cacf
-- title:
--   Small-set repair bounds with a uniform start
-- statement:
--   Title: Repair-bounds estimate with a uniformly random start
--
--   For sufficiently large k and n, let m be nonnegative and in the density range of Lemma 7.11, and fix t ≥ 0. Choose a starting assignment z uniformly, independently sample a Poisson random k-SAT formula Φ⁺ of mean m, retain its clauses satisfied by z as Φ₀, and run t random Glauber updates on Φ₀ from z. The probability that the resulting assignment X satisfies all three repair bounds for (Φ⁺, Φ₀, X) is at least 1 − exp(−ρ⁸n).
--
--   This is an open transport target; the separate fixed-start symmetry theorem turns it into the estimate for every fixed z. The sampled formula retains its original clause order and multiplicities.
--
--   Source: Chunyang Wang, Yitong Yin, Yixiao Yu, and Yiyao Zhang, *Single-Variable Connectivity in Random k-SAT*, proof of the probabilistic guarantee in Lemma 7.4 after Lemma 7.12, printed p. 65 (PDF p. 67 of STOC 2027 submission #737), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, proof of probabilistic Lemma 7.4 after Lemma 7.12, printed p. 65 (PDF p. 67), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Repair
import Definitions.Def_KSATSingleFlip_Connect_Glauber

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.11's repair bounds under a uniformly random start, the Poisson
formula law, and the planted-subformula Glauber dynamics. -/
theorem repair_bounds_uniform_start :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      m ≤ (2 : ℝ) ^ k * n / k * loosenessLambda k →
      ∀ t : ℕ,
        1 - Real.exp (-(rho k ^ 8) * n) ≤
          uexp (fun z : Fin n → Bool => poisExp (allClauses n k) m (fun l =>
            uprob fun s : Fin t → Fin n × Bool =>
              let Φ := ofList l
              let I0 := satIdx Φ z
              let X := glauberState (subF Φ I0) z s
              RepairBounds k Φ I0 X)) := by
  sorry

end KSATSingleFlip.Connect
