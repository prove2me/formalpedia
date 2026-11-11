-- Prove2me | Theorems.Thm_HamLocality237_Testing_lemma_3_9
-- name    : HamLocality237.Testing.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:22.299698+00:00
-- url     : https://prove2.me/theorems/1effc327-fa97-42b9-afc4-eeda53e41563
-- title:
--   Lemma 3.9 — absolute continuity and exact progress rate
-- statement:
--   For every continuous-time algorithm and $0<\varepsilon<1/2$, the progress function is absolutely continuous on $[0,t_f]$, differentiable almost everywhere there, and
--
--   $$P'(t)\le C_{\rm prog}\varepsilon^2\lambda(t),\qquad C_{\rm prog}=1+\eta^2/4.$$
--
--   The intensity is nonnegative as part of the algorithm model. The constant is fixed by the source operators and is independent of the algorithm, dimension, and precision.
--
--   Differences from the source:
--   - encoding: the finite-dimensional continuous-time model with a fixed unit basis state and final projective measurement → EuclideanSpace on Fin w × Qubits n, any unit initial vector, and a binary final orthogonal projection; reason: every unit vector can be selected as a basis vector; coarse-graining the final measurement gives the same binary acceptance law; finite-interval a.e. data can be extended by zero outside the interval
--   - generalization: the positive qubit count in the source model → the continuous-time statements also permit n=0; reason: the tensor and query sums retain one input site at n=0 and the dimension-independent argument applies; simulation at n=0 is input-independent and needs no query time
--   - encoding: the completed Hilbert tensors I and A ⊗ I and integral-equation evolutions → completions of actual algebraic tensor products and their Dyson evolutions; reason: the inner product and bounded one-factor maps extend to these completions; this is the same Hilbert tensor product, with factors relabeled by a finite equivalence
--   - encoding: absolute continuity and an almost-everywhere derivative inequality → AbsolutelyContinuousOnInterval and simultaneous a.e. differentiability and a deriv bound; reason: explicit differentiability excludes interpreting the total derivative at a failure point; the definition fixes the exact source constant
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Lemma 3.9, pp.21–22. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem lemma_3_9 (n : ℕ) (A : ContinuousAlgorithm n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    AbsolutelyContinuousOnInterval (progress A ε) 0 A.finalTime ∧
    (∀ᵐ t ∂volume.restrict (Set.Icc 0 A.finalTime),
      DifferentiableAt ℝ (progress A ε) t ∧
        deriv (progress A ε) t ≤ progressConstant * ε ^ 2 * A.intensity t) := by sorry

end HamLocality237.Testing
