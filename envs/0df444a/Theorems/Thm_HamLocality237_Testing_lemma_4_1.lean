-- Prove2me | Theorems.Thm_HamLocality237_Testing_lemma_4_1
-- name    : HamLocality237.Testing.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:41.82151+00:00
-- url     : https://prove2.me/theorems/3249d1a5-08a1-4794-96ed-6cb3f14810ea
-- title:
--   Lemma 4.1 — strict farness from locality with probability 2/3
-- statement:
--   Let $0<\alpha<1/2$, let $n,k$ be nonnegative integers with $8k\le n$, and suppose $\alpha^2\ge24/2^n$. Draw all $h_x$ independently from the constructed continuous law $\nu_\alpha$ and let $H=\operatorname{diag}(h_x)$. The farness event is measurable and
--
--   $$\Pr[\operatorname{dist}(H,k\text{-local})>\alpha/2]\ge2/3.$$
--
--   The inequality inside the event is strict. The statement allows $k=0$ and retains the threshold $24/2^n$. Its assumptions already imply $n\ge7$.
--
--   Differences from the source:
--   - encoding: independent continuous real entries with a strict farness event → Measure.pi of the actual spectral law, an explicitly measurable event, and ENNReal probability; reason: this is the same independent law and event; the hypotheses exclude n=0 automatically, and 8k≤n is equivalent to k≤n/8 over real numbers
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Lemma 4.1, pp.23–24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem lemma_4_1 (n k : ℕ) (α : ℝ) (hα : 0 < α) (hα' : α < 1 / 2)
    (hk : 8 * k ≤ n) (hsize : 24 / (2 : ℝ) ^ n ≤ α ^ 2) :
    MeasurableSet {h : QAlgorithms.Qubits n → ℝ |
      α / 2 < distanceFromLocality k (diagonalHamiltonian h)} ∧
    ENNReal.ofReal (2 / 3 : ℝ) ≤ hardProductMeasure n α
      {h | α / 2 < distanceFromLocality k (diagonalHamiltonian h)} := by sorry

end HamLocality237.Testing
