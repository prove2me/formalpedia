-- Prove2me | Theorems.Thm_HamLocality237_Testing_lemma_3_6
-- name    : HamLocality237.Testing.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:41.543201+00:00
-- url     : https://prove2.me/theorems/98c61698-389c-4027-80c5-bc4712c073d2
-- title:
--   Lemma 3.6 — quantitative progress from separation
-- statement:
--   For every continuous-time algorithm and $0<\varepsilon<1/2$, the source progress satisfies
--
--   $$P(t_f)\ge\tfrac12\|\Psi_F(t_f)-\Psi_Z(t_f)\|^2.$$
--
--   Consequently any fixed positive final separation gives a fixed positive final progress. The factor $1/2$ is the explicit inequality in the source proof.
--
--   Differences from the source:
--   - encoding: the finite-dimensional continuous-time model with a fixed unit basis state and final projective measurement → EuclideanSpace on Fin w × Qubits n, any unit initial vector, and a binary final orthogonal projection; reason: every unit vector can be selected as a basis vector; coarse-graining the final measurement gives the same binary acceptance law; finite-interval a.e. data can be extended by zero outside the interval
--   - generalization: the positive qubit count in the source model → the continuous-time statements also permit n=0; reason: the tensor and query sums retain one input site at n=0 and the dimension-independent argument applies; simulation at n=0 is input-independent and needs no query time
--   - encoding: the completed Hilbert tensors I and A ⊗ I and integral-equation evolutions → completions of actual algebraic tensor products and their Dyson evolutions; reason: the inner product and bounded one-factor maps extend to these completions; this is the same Hilbert tensor product, with factors relabeled by a finite equivalence
--   - reading: constant-order separation implies constant-order progress → P(tf) ≥ one half of the squared separation for every algorithm; reason: the displayed inequality in the source proof specifies all constants and implies the printed statement for every separation threshold
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Lemma 3.6 and its proof, p.17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem lemma_3_6 (n : ℕ) (A : ContinuousAlgorithm n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ‖purifiedFar A ε A.finalTime - purifiedZero A A.finalTime‖ ^ 2 / 2 ≤
      progress A ε A.finalTime := by sorry

end HamLocality237.Testing
