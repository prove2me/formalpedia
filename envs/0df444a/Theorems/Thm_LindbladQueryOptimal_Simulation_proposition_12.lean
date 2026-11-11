-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_proposition_12
-- name    : LindbladQueryOptimal.Simulation.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:55.15612+00:00
-- url     : https://prove2.me/theorems/9a80cf00-b297-4581-ac08-0ab44b8030e7
-- title:
--   Proposition 12 — Local transducer identity
-- statement:
--   Let $O_L$ be an exact positive-normalization block encoding of $L$, and let $0\le\delta\le1/2$. Use the computed $\nu,K_0,K_1$ and catalyst map $\Gamma_{\rm loc}$ from Eqs. (8), (10), (43)–(45). Then
--   $$\nu=\frac{\delta}{(1+\sqrt{1-\delta})^2},\qquad R(\psi\oplus0\oplus\widetilde O_L\Gamma_{\rm loc}\psi)=K_0\psi\oplus K_1\psi\oplus\Gamma_{\rm loc}\psi$$
--   for every input vector $\psi$. This is a restoration identity for a computed linear catalyst, not an assumption that the catalyst is physically preparable.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
--   - generalization: the exact block-encoding convention uses a positive number of encoding qubits → zero encoding qubits are also permitted when the system is one-dimensional; reason: the dimension-independent local matrix identities and estimates also apply to that case; every source instance is still included
--   - generalization: the construction in §3.1 is introduced with a positive local step → the defined zero-step endpoint is included as well; reason: the formulas remain defined at zero and recover the identity public channel and zero catalyst; every positive-step source instance is included
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Proposition 12, p. 15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem proposition_12 (n a : ℕ) (L : Op (Bits n)) (α : ℝ) (O : Op (Bits a))
      (ha : n ≤ a) (hA : exactAccess L α O (padding n a) (padding n a)) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) :
    nu δ = δ / (1 + Real.sqrt (1-δ))^2 ∧
    rotation (padding n a) (padding n a) δ *
      Matrix.fromRows (Matrix.fromRows (1 : Op (Bits n)) (0 : Op (Bits n)))
        (oracleLift O * catalyst L α δ O (padding n a) (padding n a)) =
      Matrix.fromRows (Matrix.fromRows (K0 L α δ) (K1 L α δ))
        (catalyst L α δ O (padding n a) (padding n a)) := by sorry

end LindbladQueryOptimal.Simulation
