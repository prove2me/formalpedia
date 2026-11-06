-- Prove2me | Theorems.Thm_NearLinIsing_lemma_4_4
-- name    : NearLinIsing.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:27.737732+00:00
-- url     : https://prove2.me/theorems/4e5d07e8-8909-41e2-9168-07fb7e505468
-- title:
--   Lemma 4.4 — exact cycle proposals
-- statement:
--   There is an absolute constant $C_4>0$ such that, for every graph $G$ containing a cycle with maximum degree at most $\Delta\ge3$ and every $r>0$ with $(\Delta-1)r\le1$, the concrete trial on the port graph $H$, based on (13), satisfies:
--
--   1. its output is either no candidate or the edge list of a cycle of $H$;
--   2. for every cycle $C$, $\mathbb P(\text{output }C)=w_C/|E(H)|$;
--   3. its expected work, including unsuccessful trials, is at most $C_4\log n$;
--   4. running the trial with probability $|E(H)|/(4N)$ proposes each cycle $C$ with probability $w_C/(4N)$, the insertion proposal of $P$, for every $N$ with $|E(H)|\le4N$.
--
--   Exact proposals let the chain run without ever evaluating $\sum_Cw_C$.
--
--   Differences from the source:
--   - encoding: there is a trial based on (13) → the statement is about the concrete `cycleTrial`; reason: it is the trial of the proof on p. 21, and it implies the existential
--   - generalization: expected exploration length O(log n) → expected charged work at most C₄ log n; reason: the work dominates the number of queried transitions; the proof on p. 21 bounds both
--   - encoding: G (standing in §4: G contains a cycle) → `G.HasCycle`, so n ≥ 3 and log n > 0; reason: the standing assumption of §4, p. 18
--   - encoding: the output is a random variable → measurability of the output events and of the cost is part of the conclusion; reason: otherwise the probabilities would not be meaningful
--   - encoding: H, the graph supplied by Proposition 4.1 → `portGraph G r` for a well-formed `IncGraph` G with `MaxDegLe Δ`, 3 ≤ Δ, r > 0, (Δ − 1) r ≤ 1, the trial started with clean scratch arrays; reason: the hypotheses and construction of Proposition 4.1 (pp. 18–19) in the input format of §2.6
--   - encoding: running the trial with probability |E(H)|/(4N) → the insertion clause is stated for every N with |E(H)| ≤ 4N; reason: the condition only excludes values of N for which |E(H)|/(4N) is not a probability; N = 10m satisfies it
--   - reading: O(log n) → one constant C₄, independent of Δ, G and r; reason: the stronger reading; the horizon gives Σ_{ℓ ≤ 2|E(H)|} 1/ℓ ≤ 1 + log(6m) and m ≤ n², so the constant is absolute
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Lemma 4.4 and its proof, p. 21

import Mathlib
import Definitions.Def_NearLinIsing_buildPort
import Definitions.Def_NearLinIsing_cycleTrial

open MeasureTheory
open scoped ENNReal

namespace NearLinIsing

/-- **Lemma 4.4** (Exact cycle proposals), p. 21.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Lemma 4.4 and its proof, p. 21.

There is an absolute constant `C₄ > 0` such that, for every well-formed `G` that contains a cycle,
with maximum degree at most `Δ ≥ 3`, and every `r > 0` with `(Δ − 1) r ≤ 1`, the concrete trial
`cycleTrial` on the port graph `H = portGraph G r` (based on (13)), started with clean scratch
arrays, satisfies:
1. its output is either no candidate or the edge list (without repetition) of a cycle of `H`;
2. for every cycle `C`, `P(output C) = w_C/|E(H)|`;
3. its expected work, unsuccessful trials included, is at most `C₄ log n`;
4. running the trial with probability `|E(H)|/(4N)` (`insertProposal`) proposes every cycle `C`
   with probability `w_C/(4N)`, the insertion proposal of `P`, for every `N` with `|E(H)| ≤ 4N`.

**Formalization Note.** The paper's "expected exploration length" (queried transitions) is stated
as the trial's charged work, which dominates it; the proof on p. 21 bounds both. `G` contains a
cycle (the standing assumption of §4, p. 18), so `n ≥ 3` and `log n > 0`. -/
theorem lemma_4_4 :
    ∃ C₄ : ℝ, 0 < C₄ ∧
    ∀ Δ : ℕ, 3 ≤ Δ → ∀ G : IncGraph, G.WellFormed → G.MaxDegLe Δ → G.HasCycle →
    ∀ r : ℝ, 0 < r → ((Δ : ℝ) - 1) * r ≤ 1 →
      (∀ τ : Tape, ∀ L : List ℕ,
        (runVal (cycleTrial (portGraph G r) (Scratch.init (portGraph G r))) τ).1 = some L →
          L.Nodup ∧ (∀ e ∈ L, e < (portGraph G r).ne) ∧
          (portGraph G r).IsCycle ((portGraph G r).toEdges L)) ∧
      (∀ C : (portGraph G r).Cyc,
        MeasurableSet {τ : Tape |
          ((runVal (cycleTrial (portGraph G r) (Scratch.init (portGraph G r))) τ).1.map
            (portGraph G r).toEdges) = some C.1} ∧
        tapeLaw.real {τ : Tape |
          ((runVal (cycleTrial (portGraph G r) (Scratch.init (portGraph G r))) τ).1.map
            (portGraph G r).toEdges) = some C.1} =
          (portGraph G r).cycleModel.w C / (portGraph G r).ne) ∧
      Measurable (fun τ : Tape =>
        runCost (cycleTrial (portGraph G r) (Scratch.init (portGraph G r))) τ) ∧
      ∫⁻ τ, (runCost (cycleTrial (portGraph G r) (Scratch.init (portGraph G r))) τ : ℝ≥0∞)
          ∂tapeLaw ≤ ENNReal.ofReal (C₄ * Real.log G.n) ∧
      (∀ N : ℕ, ((portGraph G r).ne : ℝ) ≤ 4 * N → ∀ C : (portGraph G r).Cyc,
        tapeLaw.real {τ : Tape |
          ((runVal (insertProposal (portGraph G r) N (Scratch.init (portGraph G r))) τ).1.map
            (portGraph G r).toEdges) = some C.1} =
          (portGraph G r).cycleModel.w C / (4 * N)) := by sorry

end NearLinIsing
