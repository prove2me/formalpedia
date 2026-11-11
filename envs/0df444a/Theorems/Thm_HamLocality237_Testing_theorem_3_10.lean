-- Prove2me | Theorems.Thm_HamLocality237_Testing_theorem_3_10
-- name    : HamLocality237.Testing.theorem_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:13.322208+00:00
-- url     : https://prove2.me/theorems/80be5072-7c67-4a25-8600-baa97515772a
-- title:
--   Theorem 3.10 — quantitative continuous-time lower bound
-- statement:
--   For every continuous-time algorithm and $0<\varepsilon<1/2$,
--
--   $$\|\Psi_F(t_f)-\Psi_Z(t_f)\|^2\le2C_{\rm prog}\varepsilon^2T,\qquad T=\int_0^{t_f}\lambda(t)\,dt.$$
--
--   Thus a final separation at least $\delta>0$ forces $T\ge\delta^2/(2C_{\rm prog}\varepsilon^2)$. This fixes the uniform dependence behind both constant-order terms in the printed theorem.
--
--   Differences from the source:
--   - encoding: the finite-dimensional continuous-time model with a fixed unit basis state and final projective measurement → EuclideanSpace on Fin w × Qubits n, any unit initial vector, and a binary final orthogonal projection; reason: every unit vector can be selected as a basis vector; coarse-graining the final measurement gives the same binary acceptance law; finite-interval a.e. data can be extended by zero outside the interval
--   - generalization: the positive qubit count in the source model → the continuous-time statements also permit n=0; reason: the tensor and query sums retain one input site at n=0 and the dimension-independent argument applies; simulation at n=0 is input-independent and needs no query time
--   - encoding: the completed Hilbert tensors I and A ⊗ I and integral-equation evolutions → completions of actual algebraic tensor products and their Dyson evolutions; reason: the inner product and bounded one-factor maps extend to these completions; this is the same Hilbert tensor product, with factors relabeled by a finite equivalence
--   - reading: constant-order final separation requires Ω(1/ε²) total time → squared separation ≤ 2 Cprog ε² T for every algorithm; reason: this is the exact comparison of the preceding progress inequalities in the source proof; it implies the theorem for every fixed separation constant
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Theorem 3.10 and proof, p.23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem theorem_3_10 (n : ℕ) (A : ContinuousAlgorithm n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ‖purifiedFar A ε A.finalTime - purifiedZero A A.finalTime‖ ^ 2 ≤
      2 * progressConstant * ε ^ 2 * A.time := by sorry

end HamLocality237.Testing
