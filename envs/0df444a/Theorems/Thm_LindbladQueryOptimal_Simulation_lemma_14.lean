-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_14
-- name    : LindbladQueryOptimal.Simulation.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:51.925561+00:00
-- url     : https://prove2.me/theorems/c570d056-5fb9-40a1-8151-9fc1c48bc02c
-- title:
--   Lemma 14 — Private Block
-- statement:
--   Let $S^\circ$ be the actual chronological product of the lifted single-jump rotations, let $O$ be the time-controlled Hermitian oracle lift, and let $\mathcal V$ be the valid private space with all future history entries zero. The private block of $S^\circ$ and the oracle both preserve $\mathcal V$. On this space, with the independently defined correction kernels of Eqs. (76)–(77) and $P=\bigoplus_{\ell,h}V_1V_1^\dagger$,
--   $$S_{C\leftarrow C}=S^\circ_{C\leftarrow C}O=i(I-P-\Delta_R-\Delta_J)O=i(I-P)O-i(\Delta_R+\Delta_J)O.$$
--   The invariance claims are stated by vanishing matrix coefficients outside the valid output coordinates; the block products act on the valid subtype. The full rotation retains the norm-one jump-input transition.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
--   - generalization: the exact block-encoding convention uses a positive number of encoding qubits → zero encoding qubits are also permitted when the system is one-dimensional; reason: the dimension-independent local matrix identities and estimates also apply to that case; every source instance is still included
--   - encoding: an invariant subspace and operator restrictions to it → a subtype of valid coordinates and explicit zero coefficients outside that subtype; reason: the coordinate span is exactly Eq. (72), with invariance asserted separately
--   - generalization: the construction in §3.1 is introduced with a positive local step → the defined zero-step endpoint is included as well; reason: the formulas remain defined at zero and recover the identity public channel and zero catalyst; every positive-step source instance is included
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 14, p. 20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Histories

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_14 (n a r : ℕ) (hr : 0 < r) (ha : n ≤ a) (L : Op (Bits n)) (α : ℝ) (O : Op (Bits a))
    (hA : exactAccess L α O (padding n a) (padding n a)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) :

    let R := singleRotation (padding n a) (padding n a) δ
    let P := singleP (padding n a)
    let U := restrictedOracle (r := r) (m := 1) (oracleLift O)
    let A := privateRotation (r := r) R
    (∀ (x : Private r 1 (Sum (Bits a) (Bits a))) (y : Valid r 1 (Sum (Bits a) (Bits a))),
      ¬ valid x → globalRotation R (.inr x) (.inr y.val) = 0) ∧
    (∀ (x : Private r 1 (Sum (Bits a) (Bits a))) (y : Valid r 1 (Sum (Bits a) (Bits a))),
      ¬ valid x → globalOracle (oracleLift O) x y.val = 0) ∧
    A * U = (Complex.I • (1 - jumpProjection P - singleDeltaR (r := r) (padding n a) δ - singleDeltaJ (r := r) (padding n a) (padding n a) δ)) * U ∧
    A * U = (Complex.I • (1 - jumpProjection P)) * U -
      (Complex.I • (singleDeltaR (r := r) (padding n a) δ + singleDeltaJ (r := r) (padding n a) (padding n a) δ)) * U := by sorry

end LindbladQueryOptimal.Simulation
