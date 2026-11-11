-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_13
-- name    : LindbladQueryOptimal.Simulation.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:23.878505+00:00
-- url     : https://prove2.me/theorems/f50ec202-3786-4020-82f9-403471eb5e01
-- title:
--   Lemma 13 — Catalyst size
-- statement:
--   For an exact block encoding of $L$ with positive normalization, and $0\le\delta\le1/2$, the local catalyst map computed in Eqs. (43)–(45) obeys
--   $$\|\Gamma_{\rm loc}\|^2\le2\delta.$$
--   The norm is the spectral norm of the full map into the padded private register. This bound permits orthogonal private labels to control the global catalyst norm.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
--   - generalization: the exact block-encoding convention uses a positive number of encoding qubits → zero encoding qubits are also permitted when the system is one-dimensional; reason: the dimension-independent local matrix identities and estimates also apply to that case; every source instance is still included
--   - generalization: the construction in §3.1 is introduced with a positive local step → the defined zero-step endpoint is included as well; reason: the formulas remain defined at zero and recover the identity public channel and zero catalyst; every positive-step source instance is included
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 13, p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_13 (n a : ℕ) (L : Op (Bits n)) (α : ℝ) (O : Op (Bits a))
      (ha : n ≤ a) (hA : exactAccess L α O (padding n a) (padding n a)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) :
    spectral (catalyst L α δ O (padding n a) (padding n a))^2 ≤ 2*δ := by sorry

end LindbladQueryOptimal.Simulation
