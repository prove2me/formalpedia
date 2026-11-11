-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_proposition_17
-- name    : LindbladQueryOptimal.Simulation.proposition_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:51.578036+00:00
-- url     : https://prove2.me/theorems/dd25b570-4054-48e8-8180-81fd9bf7c5bf
-- title:
--   Proposition 17 — Factorial private-block decay
-- statement:
--   For a single jump with its exact positive-normalization block encoding, let $\tau\ge0$, and let $q,r$ be integers with $q\ge16e^2(1+\tau)$ and $r\ge4q$. Set $\delta=\tau/r$, and restrict the computed global private block to its valid space. Then
--   $$\left\|p_{\rm annih}(S_{C\leftarrow C})^q\big|_{\mathcal V}\right\|\le\left(176e\sqrt{\tau/q}\right)^q.$$
--   The numerical choices are supplied by the proof on p. 24. They are for the single-jump bound; the enlarged constants for the combined model are not identified with them.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
--   - generalization: the exact block-encoding convention uses a positive number of encoding qubits → zero encoding qubits are also permitted when the system is one-dimensional; reason: the dimension-independent local matrix identities and estimates also apply to that case; every source instance is still included
--   - encoding: universal constants C and C* in the proposition → C=16e² and C*=176e; reason: the proof on p. 24 explicitly supplies these choices; no combined-model constant is inferred from them
--   - generalization: the private-block construction is introduced for positive local time → zero normalized time is also included; reason: the cancellation polynomial vanishes exactly at zero time, and the positive degree threshold excludes division by zero
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Proposition 17, p. 23; proof constants p. 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Histories

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem proposition_17 (n a : ℕ) (ha : n ≤ a) (L : Op (Bits n)) (α : ℝ)
    (O : Op (Bits a)) (hA : exactAccess L α O (padding n a) (padding n a))
    (τ : ℝ) (hτ : 0 ≤ τ) (q r : ℕ)
    (hq : 16 * Real.exp 1 ^ 2 * (1+τ) ≤ q) (hr : 4*q ≤ r) :
    let R := singleRotation (padding n a) (padding n a) (τ/r)
    let A := privateRotation (r := r) R *
      restrictedOracle (r := r) (m := 1) (oracleLift O)
    spectral ((annihilate A)^q) ≤
      (176 * Real.exp 1 * Real.sqrt (τ/q))^q := by sorry

end LindbladQueryOptimal.Simulation
