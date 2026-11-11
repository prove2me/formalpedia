-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_3
-- name    : LindbladQueryOptimal.Simulation.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:48.80059+00:00
-- url     : https://prove2.me/theorems/a043ee51-cfc4-42b2-9596-457f76fb4fa8
-- title:
--   Lemma 3 — Uniform first-order error
-- statement:
--   Let $L$ act on an $n$-qubit system and let $O_L$ be an exact $\alpha$-block encoding on $a\ge n$ qubits, with $\alpha>0$. Let $\Phi_\delta$ be the computed Kraus map of Eq. (9), and $D_L(X)=LXL^\dagger-\tfrac12\{L^\dagger L,X\}$. There is a positive absolute constant $C$, independent of all this data, such that for every $0\le\delta\le1/2$,
--   $$\left\|\Phi_\delta-\exp((\delta/\alpha^2)D_L)\right\|_\diamond\le C\delta^2.$$
--   This controls one local dissipative step uniformly in the oracle normalization and system dimension.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
--   - encoding: the unhalved stabilized induced trace norm → the published ENNReal unit-ball supremum with input-dimensional reference; reason: homogeneity gives the same norm on the linear maps in these statements, without a factor of one half
--   - encoding: a universal positive error constant → a positive existential constant before all dimensions, oracles, normalizations and times; reason: makes the source uniformity explicit rather than allowing instance-dependent constants
--   - generalization: the exact block-encoding convention uses a positive number of encoding qubits → zero encoding qubits are also permitted when the system is one-dimensional; reason: the dimension-independent local matrix identities and estimates also apply to that case; every source instance is still included
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 3, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_3 : ∃ C : ℝ, 0 < C ∧ ∀ (n a : ℕ) (L : Op (Bits n)) (α : ℝ) (O : Op (Bits a))
      (ha : n ≤ a) (hA : exactAccess L α O (padding n a) (padding n a)) (δ : ℝ),
    0 ≤ δ → δ ≤ 1/2 →
    RandomDimReduction.Channel.diamond (fun X => localChannel L α δ X -
      dissipativeEvolution L (δ / α^2) X) ≤ ENNReal.ofReal (C * δ^2) := by sorry

end LindbladQueryOptimal.Simulation
