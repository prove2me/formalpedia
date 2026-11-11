-- Prove2me | Theorems.Thm_HamLocality237_Testing_lemma_3_5
-- name    : HamLocality237.Testing.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:34.390196+00:00
-- url     : https://prove2.me/theorems/73b9a5f1-587c-4124-90e6-e013523fe485
-- title:
--   Lemma 3.5 — fixed random input and the zero evolution
-- statement:
--   For every continuous-time algorithm, $0<\varepsilon<1/2$, and $t\in[0,t_f]$, the state as a function of the independent input table is measurable and integrable. For every bounded operator $X$ on the finite-dimensional algorithm space,
--
--   $$\langle\Psi_F(t),(X\otimes I)\Psi_F(t)\rangle=
--   \mathbb E_{h\sim\nu_\varepsilon^{\otimes2^n}}\langle\psi_H(t),X\psi_H(t)\rangle.$$
--
--   Each scalar expectation is integrable. Also
--
--   $$\Psi_Z(t)=\psi_0(t)\otimes\Omega.$$
--
--   The first identity is exactly the partial-trace identity, expressed by testing against all algorithm operators. Both assertions use the same fixed random input throughout the evolution.
--
--   Differences from the source:
--   - encoding: the finite-dimensional continuous-time model with a fixed unit basis state and final projective measurement → EuclideanSpace on Fin w × Qubits n, any unit initial vector, and a binary final orthogonal projection; reason: every unit vector can be selected as a basis vector; coarse-graining the final measurement gives the same binary acceptance law; finite-interval a.e. data can be extended by zero outside the interval
--   - generalization: the positive qubit count in the source model → the continuous-time statements also permit n=0; reason: the tensor and query sums retain one input site at n=0 and the dimension-independent argument applies; simulation at n=0 is input-independent and needs no query time
--   - encoding: the completed Hilbert tensors I and A ⊗ I and integral-equation evolutions → completions of actual algebraic tensor products and their Dyson evolutions; reason: the inner product and bounded one-factor maps extend to these completions; this is the same Hilbert tensor product, with factors relabeled by a finite equivalence
--   - encoding: partial trace equals the expectation of density operators → duality against every bounded algorithm operator, with genuine product-measure expectations and explicit integrability; reason: the algorithm space is finite-dimensional, so all matrix entries and hence the entire density matrix are determined by these tests
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Lemma 3.5, Eq. (13), p.16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem lemma_3_5 (n : ℕ) (A : ContinuousAlgorithm n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (t : ℝ) (ht : t ∈ Set.Icc 0 A.finalTime) :
    AEStronglyMeasurable (fun h => A.state h t) (hardProductMeasure n ε) ∧
    Integrable (fun h => A.state h t) (hardProductMeasure n ε) ∧
    (∀ X : A.Space →L[ℂ] A.Space,
      Integrable (fun h => inner ℂ (A.state h t) (X (A.state h t))) (hardProductMeasure n ε) ∧
      inner ℂ (purifiedFar A ε t) (jointLift A X 1 (purifiedFar A ε t)) =
        ∫ h, inner ℂ (A.state h t) (X (A.state h t)) ∂hardProductMeasure n ε) ∧
    purifiedZero A t = jointProduct A (A.state (fun _ => 0) t) (inputVacuum n) := by sorry

end HamLocality237.Testing
