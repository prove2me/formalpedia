-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_15
-- name    : LindbladQueryOptimal.Simulation.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:03.036567+00:00
-- url     : https://prove2.me/theorems/5a0bb3d6-f5dd-412e-86c2-d85c96504329
-- title:
--   Lemma 15 — Algebraic word norm bound
-- statement:
--   Let $r>0$, $0\le\delta\le1/2$, and let a word $\sigma$ have $u$ regular letters and $v$ jump letters. Between its correction factors insert arbitrary fixed contractions $D_0,\ldots,D_d$ preserving every time-history block, and form $W_\sigma=D_d\Delta_{\sigma_d}\cdots D_1\Delta_{\sigma_1}D_0$. Then both bounds hold:
--   $$\|W_\sigma\|\le\delta^{u+v/2}\binom{r+u-1}{u}\binom rv^{1/2}\le\delta^u\binom{r+u}{u}\left(\delta^v\binom rv\right)^{1/2}.$$
--   If $v>r$, the operator and both displayed bounds are zero. This controls the single-jump path kernels defined directly from the source's chronological amplitudes.
--
--   Differences from the source:
--   - encoding: finite qubit spaces and equalities of operators on all vectors → binary-word matrix indices and matrix equalities; reason: coordinate representation of the same finite-dimensional operators
--   - generalization: the exact block-encoding convention uses a positive number of encoding qubits → zero encoding qubits are also permitted when the system is one-dimensional; reason: the dimension-independent local matrix identities and estimates also apply to that case; every source instance is still included
--   - encoding: the nonnegative fractional power δ^(u+v/2) → δ^u times (sqrt δ)^v; reason: identical on the stated nonnegative-step domain and avoids fractional exponent conventions
--   - generalization: the construction in §3.1 is introduced with a positive local step → the defined zero-step endpoint is included as well; reason: the formulas remain defined at zero and recover the identity public channel and zero catalyst; every positive-step source instance is included
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 15, p. 21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Histories

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_15 (n a r : ℕ) (ha : n ≤ a) (hr : 0 < r) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) (σ : List Bool)
    (D : ℕ → Op (Valid r 1 (Sum (Bits a) (Bits a))))
    (hD : ∀ i ≤ σ.length, historyPreserving (D i) ∧ spectral (D i) ≤ 1) :
    let R := singleRotation (padding n a) (padding n a) δ
    let P := singleP (padding n a)
    let u := σ.count false
    let v := σ.count true
    let b₁ := δ^u * (Real.sqrt δ)^v * (Nat.choose (r+u-1) u : ℝ) *
      Real.sqrt (Nat.choose r v : ℝ)
    let b₂ := δ^u * (Nat.choose (r+u) u : ℝ) *
      Real.sqrt (δ^v * (Nat.choose r v : ℝ))
    spectral (singleWord (padding n a) (padding n a) δ σ D) ≤ b₁ ∧ b₁ ≤ b₂ ∧
      (r < v → singleWord (padding n a) (padding n a) δ σ D = 0 ∧ b₁ = 0 ∧ b₂ = 0) := by sorry

end LindbladQueryOptimal.Simulation
