-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_16
-- name    : LindbladQueryOptimal.Simulation.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:43.55336+00:00
-- url     : https://prove2.me/theorems/3652c7f7-eace-4c2e-8095-476d5ec17f79
-- title:
--   Lemma 16 — Error Cancellation Polynomial
-- statement:
--   For the constructed single-jump private space and oracle, put $A=i(I-P)O$ on the invariant valid space $\mathcal V$. With $p_{\rm annih}(Z)=(Z^2+Z^4)/2$,
--   $$A^2=-I+P+OPO,\qquad p_{\rm annih}(A)=0.$$
--   Also $\|p_{\rm annih}(B)\|\le1$ for every contraction $B$ on that space. These assertions concern the actual computed projection and oracle; their algebraic properties are not supplied as extra theorem hypotheses.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
--   - generalization: the exact block-encoding convention uses a positive number of encoding qubits → zero encoding qubits are also permitted when the system is one-dimensional; reason: the dimension-independent local matrix identities and estimates also apply to that case; every source instance is still included
--   - generalization: the construction in §3.1 is introduced with a positive local step → the defined zero-step endpoint is included as well; reason: the formulas remain defined at zero and recover the identity public channel and zero catalyst; every positive-step source instance is included
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 16, p. 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Histories

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_16 (n a r : ℕ) (hr : 0 < r) (ha : n ≤ a) (L : Op (Bits n)) (α : ℝ) (O : Op (Bits a))
    (hA : exactAccess L α O (padding n a) (padding n a)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) :

    let R := singleRotation (padding n a) (padding n a) δ
    let P := singleP (padding n a)
    let U := restrictedOracle (r := r) (m := 1) (oracleLift O)
    let A := privateRotation (r := r) R
    let Q := jumpProjection P
    let B := (Complex.I • (1-Q)) * U
    B^2 = -1 + Q + U * Q * U ∧ annihilate B = 0 ∧
      (∀ Z : Op (Valid r 1 (Sum (Bits a) (Bits a))),
        spectral Z ≤ 1 → spectral (annihilate Z) ≤ 1) := by sorry

end LindbladQueryOptimal.Simulation
