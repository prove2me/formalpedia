-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_nonmetric_cycle_hitting
-- name    : MetricTesting.Characterization.Supplement.nonmetric_cycle_hitting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:24:43.071988+00:00
-- url     : https://prove2.me/theorems/6e830bc6-91a3-4ef3-bff4-01161989e1c1
-- title:
--   Lemma 5.12 — Hitting shortest nonmetric cycles
-- statement:
--   Let $G$ be a positively weighted simple graph on $n$ vertices, with $h=\binom n2-|E(G)|$ holes. Let $r\ge4$ be an integer, and suppose no nonmetric cycle has length less than $r$. Then some subset $S$ of specified edges satisfies
--
--   $$|S|\le rh,$$
--
--   and meets every nonmetric simple $r$-cycle. A nonmetric cycle has one edge strictly longer than the sum of its remaining edges.
--
--   The graph is represented by the published partial-array carrier over arbitrary positive real weights; unspecified pairs are precisely its holes. The result provides the exact deletion factor needed for bounded metric completion, without rationality or connectedness assumptions.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: positively weighted simple graph → a partial array over positive reals and its specified simple graph; reason: specified pairs are exactly edges, with arbitrary positive real weights; all other pairs are holes
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 22, Lemma 5.12 (PDF p. 23); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_completion

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem nonmetric_cycle_hitting (n r : ℕ) (hn : 1 ≤ n) (hr : 4 ≤ r)
    (A : PartialArray PositiveValues n)
    (hshort : ∀ l : ℕ, l < r → ∀ E : Finset (Edge n), ¬ NonmetricCycle A l E) :
    ∃ S : Finset (Edge n), S ⊆ Specified A ∧ S.card ≤ r * (Holes A).card ∧
      ∀ E : Finset (Edge n), NonmetricCycle A r E → (S ∩ E).Nonempty := by sorry

end MetricTesting.Characterization.Supplement
