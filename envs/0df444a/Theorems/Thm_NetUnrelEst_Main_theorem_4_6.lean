-- Prove2me | Theorems.Thm_NetUnrelEst_Main_theorem_4_6
-- name    : NetUnrelEst.Main.theorem_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:43.450733+00:00
-- url     : https://prove2.me/theorems/c6aeabb2-961e-41ec-96d7-eba46a06acf0
-- title:
--   Theorem 4.6 — one complete run: W ≥ 0, EW = u, EW² ≤ Cu², expected time O((s + n)H²)
-- statement:
--   On the reduced input (a connected graph with $n$ vertices and $s$ edges, no loops or parallel edges, $0<p_e<1$, $n\ge n_0$), let $H=\log(8n)$. One complete run of the faster algorithm returns $W\ge0$ with
--   $$\mathbb EW=u,\qquad \mathbb EW^2\le Cu^2,$$
--   in expected time $O((s+n)H^2)$ after deterministic input preprocessing.
--
--   One run is a nonnegative unbiased estimator with constant relative variance in near-linear expected time. Theorem 1.1 follows by the amplification of Lemma J.1.
--
--   **Formalization Note.** The run is one admissible program of the extended machine. Its input is the reduced graph ($n$, $s$, $W$ and the endpoints in integer memory, $p_1,\dots,p_s$ in real memory), which is the meaning of "after deterministic input preprocessing". $W$ is real output $0$ ($0$ on a non-halting run). $\mathbb EW$ is a Bochner integral with integrability as a conclusion, $\mathbb EW^2$ is a lintegral, and the expected work is a lintegral. $C$, $n_0$ and $c_w$ are universal.
--
--   Differences from the source:
--   - reading: a randomized algorithm with an expected-time bound (no machine named) → an admissible program of the published randomized real RAM extended by capped word instructions, for every word size W ≥ c_w⌈log₂(n + s + 2)⌉ given in the input; reason: the paper uses machine words (App. G.3.2, Corollary G.5) on a unit-cost randomized RAM; the existential is over one program fixed before the input
--   - encoding: O((s + n)H²), C, and the standing n ≥ n₀ of §2.1 → ∃ explicit constants quantified before every input; reason: the meaning of O(·) and of 'there are constants'; the constants are uniform over all inputs
--   - encoding: 'after deterministic input preprocessing' → the program's input is the reduced graph (IsReduced) with its own n, s; reason: the time bound excludes the reduction of §2.1, which is exactly what the reduced input means
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 25, Theorem 4.6

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelEst_Main_CutSums
import Definitions.Def_NetUnrelEst_Main_WordMachine

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Theorem 4.6.** There are constants `C > 0`, `n₀`, `c_w` and one admissible program such that,
on every reduced input (connected, no loops, no parallel edges, `0 < p_e < 1`) with `n ≥ n₀`
vertices and `s` edges and every word size `W ≥ c_w ⌈log₂(n + s + 2)⌉`, one complete run returns
`W ≥ 0` with `EW = u`, `EW² ≤ Cu²`, in expected time `C (s + n) H²`, `H = log(8n)`. Sun 2027,
p. 25, Theorem 4.6. -/
theorem theorem_4_6 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ cw : ℕ, ∃ P : WProgram, WAdmissible P ∧
      ∀ {n s : ℕ} (ends : Ends n s) (p : Fin s → ℝ), IsReduced ends p → n₀ ≤ n →
        ∀ W : ℕ, cw * Nat.clog 2 (n + s + 2) ≤ W →
          wOnEveryHalt W P (initState noOracle (graphInts W ends) (List.ofFn p))
              (fun st => 0 ≤ outReal st 0) ∧
          MeasureTheory.Integrable
              (wOutput W P (initState noOracle (graphInts W ends) (List.ofFn p))) jointLaw ∧
          ∫ ω, wOutput W P (initState noOracle (graphInts W ends) (List.ofFn p)) ω ∂jointLaw =
              unrel ends p ∧
          ∫⁻ ω, ENNReal.ofReal
              (wOutput W P (initState noOracle (graphInts W ends) (List.ofFn p)) ω ^ 2) ∂jointLaw ≤
            ENNReal.ofReal (C * unrel ends p ^ 2) ∧
          wExpectedWork W P (initState noOracle (graphInts W ends) (List.ofFn p)) ≤
            ENNReal.ofReal (C * ((s : ℝ) + n) * Real.log (8 * n) ^ 2) := by sorry

end NetUnrelEst.Main
