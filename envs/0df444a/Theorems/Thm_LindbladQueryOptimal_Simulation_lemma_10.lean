-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_10
-- name    : LindbladQueryOptimal.Simulation.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:31.806367+00:00
-- url     : https://prove2.me/theorems/a7cecd4c-98a4-47a5-be18-9646c3ea0469
-- title:
--   Lemma 10 — R is unitary
-- statement:
--   For the padded embeddings on an $n$-qubit system and an $a\ge n$ qubit encoding register, let $R$ be exactly the three-sector rotation of Eq. (46). For $0\le\delta\le1/2$,
--   $$R^\dagger R=I,\qquad RR^\dagger=I.$$
--   Unitarity is a conclusion about the explicit rotation matrix, not a field of its definition. The public no-jump, public jump and private sectors remain distinct.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
--   - generalization: the exact block-encoding convention uses a positive number of encoding qubits → zero encoding qubits are also permitted when the system is one-dimensional; reason: the dimension-independent local matrix identities and estimates also apply to that case; every source instance is still included
--   - generalization: the construction in §3.1 is introduced with a positive local step → the defined zero-step endpoint is included as well; reason: the formulas remain defined at zero and recover the identity public channel and zero catalyst; every positive-step source instance is included
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 10, p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_10 (n a : ℕ) (ha : n ≤ a) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) :
    unitary (rotation (padding n a) (padding n a) δ) := by sorry

end LindbladQueryOptimal.Simulation
