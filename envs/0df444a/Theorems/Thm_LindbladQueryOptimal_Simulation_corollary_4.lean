-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_corollary_4
-- name    : LindbladQueryOptimal.Simulation.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:45.596281+00:00
-- url     : https://prove2.me/theorems/94acb27a-94bb-4087-90e3-31a5f13b4ad9
-- title:
--   Corollary 4 — Time discretization
-- statement:
--   Let $L$ have an exact $\alpha$-block encoding, where $\alpha>0$. Let $t\ge0$ and let $r$ be a positive integer with $r\ge2\alpha^2t$. Set $\delta=\alpha^2t/r$. A positive absolute constant $C$ can be chosen independently of the system, oracle, $\alpha,t,r$, so that
--   $$\left\|\Phi_\delta^r-\exp(tD_L)\right\|_\diamond\le C\alpha^4t^2/r.$$
--   The iterate is the actual composition of the Kraus map, and the comparator is the actual dissipator exponential. This separates discretization error from catalyst-removal error.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
--   - encoding: the unhalved stabilized induced trace norm → the published ENNReal unit-ball supremum with input-dimensional reference; reason: homogeneity gives the same norm on the linear maps in these statements, without a factor of one half
--   - encoding: a universal positive error constant → a positive existential constant before all dimensions, oracles, normalizations and times; reason: makes the source uniformity explicit rather than allowing instance-dependent constants
--   - generalization: the exact block-encoding convention uses a positive number of encoding qubits → zero encoding qubits are also permitted when the system is one-dimensional; reason: the dimension-independent local matrix identities and estimates also apply to that case; every source instance is still included
--   - encoding: the step count in the quotient defining the local time step → an explicitly positive natural number r; reason: excludes the undefined division at r=0; includes t=0 with any positive step count
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Corollary 4, p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem corollary_4 : ∃ C : ℝ, 0 < C ∧ ∀ (n a : ℕ) (L : Op (Bits n)) (α : ℝ) (O : Op (Bits a))
      (ha : n ≤ a) (hA : exactAccess L α O (padding n a) (padding n a)) (t : ℝ) (r : ℕ),
    0 ≤ t → 0 < r → 2 * α^2 * t ≤ r →
    RandomDimReduction.Channel.diamond (fun X =>
      (localChannel L α (α^2*t/r))^[r] X - dissipativeEvolution L t X) ≤
      ENNReal.ofReal (C * α^4 * t^2 / r) := by sorry

end LindbladQueryOptimal.Simulation
