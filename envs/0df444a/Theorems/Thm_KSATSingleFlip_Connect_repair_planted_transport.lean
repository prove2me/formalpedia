-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_planted_transport
-- name    : KSATSingleFlip.Connect.repair_planted_transport
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T05:49:23.45905+00:00
-- url     : https://prove2.me/theorems/ad948c86-f548-43d9-b815-b287786fb956
-- title:
--   Transport of planted repair bounds to uniform-start Glauber dynamics
-- statement:
--   Title: Transport from the planted small-set event to the uniform-start Glauber law
--
--   Fix n and k with 1 ≤ k ≤ n, a nonnegative Poisson mean m, and t Glauber steps. For every assignment x, sample independently a Poisson formula Φ₀ consisting of clauses satisfied by x, with mean m(1 − 2⁻ᵏ), and a full Poisson formula G of mean m. Consider the event that all three repair bounds hold for every formula obtained by appending a subformula of G to Φ₀. The uniform average over x of the probability of this event is at most the probability that the actual uniform-start experiment satisfies the three repair bounds.
--
--   This is the precise unproved transport step needed to apply Lemma 7.11. It includes Poisson thinning, conditional stationarity, and invariance under reordering clause occurrences. It is stated for the exact ordered-list model and preserves multiplicity.
--
--   Source: Chunyang Wang, Yitong Yin, Yixiao Yu, and Yiyao Zhang, *Single-Variable Connectivity in Random k-SAT*, the proof of the probabilistic guarantee in Lemma 7.4 after Lemma 7.12, printed p. 65 (PDF p. 67 of STOC 2027 submission #737), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, proof of probabilistic Lemma 7.4 after Lemma 7.12, printed p. 65 (PDF p. 67), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Repair
import Definitions.Def_KSATSingleFlip_Connect_Glauber

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Transport the universal planted-model repair-bounds event of Lemma 7.11
to the uniform-start Poisson/Glauber experiment. -/
theorem repair_planted_transport {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (t : ℕ) :
    uexp (fun x : Fin n → Bool =>
      poisExp (clausesSatBy (k := k) (fun _ : Fin 1 => x)) (m * (1 - 1 / (2 : ℝ) ^ k))
        (fun l0 => poisProb (allClauses n k) m (fun g =>
          ∀ I : Finset (Fin (ofList g).length),
            RepairBounds k (ofList l0 ++ subF (ofList g) I)
              (Finset.univ.filter fun c => c.val < (ofList l0).length) x))) ≤
    uexp (fun z : Fin n → Bool => poisExp (allClauses n k) m (fun l =>
      uprob fun s : Fin t → Fin n × Bool =>
        let Φ := ofList l
        let I0 := satIdx Φ z
        let X := glauberState (subF Φ I0) z s
        RepairBounds k Φ I0 X)) := by
  sorry

end KSATSingleFlip.Connect
