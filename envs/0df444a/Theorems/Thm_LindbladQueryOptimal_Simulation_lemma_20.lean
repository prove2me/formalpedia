-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_20
-- name    : LindbladQueryOptimal.Simulation.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:25.915829+00:00
-- url     : https://prove2.me/theorems/7c45d1ce-1608-4264-a7ef-643bdfe623d6
-- title:
--   Lemma 20 — Extended private-path decomposition
-- statement:
--   Take a Hermitian Hamiltonian, a nonempty finite family of arbitrary jump operators, their individual exact positive-normalization block encodings, $t>0$, and $r\ge2\tau$, where $\tau=t(\alpha_H+\sum_j\alpha_j^2)$. Set $\delta_H=\alpha_Ht/r$, $\delta_D=(\sum_j\alpha_j^2)t/r$ and $\delta_L=\tau/r$. Construct the stacked oracle, the Hamiltonian-then-dissipative rotations, and their chronological product from these inputs. On the valid future-zero private space, let $P$ be $V_1V_1^\dagger$ in the dissipative sector and zero in the Hamiltonian sector. The computed lower-triangular path kernels satisfy
--   $$S^\circ_{C\leftarrow C}=i(I-P-\Delta_R-\Delta_J),\quad S_{C\leftarrow C}=i(I-P-\Delta_R-\Delta_J)O_{\rm comp},\quad PO_{\rm comp}P=0.$$
--   Their regular diagonal is exactly Eq. (123), including its lower-left same-time path; the jump diagonal and every above-diagonal block vanish. There is a positive absolute $C_0$, before all instances, with
--   $$\|[\Delta_R]_{j,j}\|\le C_0\delta_L,\quad \|[\Delta_R]_{i,j}\|\le C_0\delta_Le^{-\delta_L(i-j-1)/2},\quad \|[\Delta_J]_{i,j}\|\le C_0\sqrt{\delta_L}e^{-\delta_L(i-j-1)/2}\quad(i>j).$$
--   The private rotation and oracle preserve the valid space. Regular paths retain the existing history and append only zeros as time advances; jump paths strictly advance time, append one jump, and coherently write its individual type at the departure time. The actual jump branch selected by the output history determines each jump-kernel coefficient; jump types are retained inside each time block.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert operators and direct sums → complex matrices indexed by finite types and sum types; reason: coordinate representation preserves every source instance and the spectral norm
--   - encoding: the stacked unitary is obtained by known amplitude preparation and controlled individual oracles → a computed unitary extension on the direct sum of the padded individual registers and a reference input sector; reason: this chooses one known state-preparation extension and fixes all unused padding; no free stacked access or source-absent operator hypothesis is introduced
--   - encoding: operators on the invariant valid subspace, with histories grouped by binary jump occurrence → the coordinate subtype of all valid labeled histories, with whole time blocks and explicit coefficients for each jump type; reason: this is the same direct sum; all compatible individual jump labels remain in each block, and invariance of the full operators is asserted
--   - encoding: there are lower-triangular path operators specified by departure paths in the proof → the independently computed local-departure/return kernels satisfy all stated identities and bounds; reason: uses the operators constructed by the source proof rather than arbitrary variables satisfying the conclusion
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 20, pp. 31–32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Combined

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_20 : ∃ C0 : ℝ, 0 < C0 ∧
    ∀ (n m aH : ℕ) (a : Fin m → ℕ), 0 < m → n ≤ aH → (∀ j, n ≤ a j) →
      0 < aH → (∀ j, 0 < a j) →
      ∀ (H : Op (Bits n)) (L : Fin m → Op (Bits n))
        (αH : ℝ) (α : Fin m → ℝ) (OH : Op (Bits aH)) (OL : ∀ j, Op (Bits (a j))),
        Hᴴ = H → exactAccess H αH OH (padding n aH) (padding n aH) →
        (∀ j, exactAccess (L j) (α j) (OL j) (padding n (a j)) (padding n (a j))) →
        ∀ (t : ℝ) (r : ℕ), 0 < t → 0 < r → 2 * (t * normalization αH α) ≤ r →
        let δH := αH*t/r
        let δD := dissipativeNormalization α*t/r
        let δL := t * normalization αH α / r
        let M := combinedRotation (n := n) (aH := aH) a δH δD
        let O := combinedOracle (n := n) a α OH OL
        let A := privateRotation (r := r) M
        let U := restrictedOracle (r := r) (m := m) O
        let P := jumpProjection (r := r) (m := m) (combinedP (n := n) (aH := aH) a)
        let DR := combinedDeltaR (n := n) (aH := aH) (r := r) a δH δD
        let DJ := combinedDeltaJ (n := n) (aH := aH) (r := r) a δH δD
        (∀ (x : Private r m (CombinedPrivate n m aH a))
            (y : Valid r m (CombinedPrivate n m aH a)),
          ¬ valid x → globalRotation M (.inr x) (.inr y.val) = 0) ∧
        (∀ (x : Private r m (CombinedPrivate n m aH a))
            (y : Valid r m (CombinedPrivate n m aH a)),
          ¬ valid x → globalOracle O x y.val = 0) ∧
        A = Complex.I • (1-P-DR-DJ) ∧
        A*U = (Complex.I • (1-P-DR-DJ))*U ∧ P*U*P = 0 ∧
        (∀ x y : Valid r m (CombinedPrivate n m aH a), x.val.1 = y.val.1 →
          DR x y = if x.val.2.1 = y.val.2.1 then
            combinedDiagonal a δH δD x.val.2.2 y.val.2.2 else 0) ∧
        (∀ j : Fin r, timeBlock j j DJ = 0 ∧ spectral (timeBlock j j DR) ≤ C0*δL) ∧
        (∀ i j : Fin r, i < j → timeBlock i j DR = 0 ∧ timeBlock i j DJ = 0) ∧
        (∀ i j : Fin r, j < i →
          spectral (timeBlock i j DR) ≤
            C0 * δL * Real.exp (-δL*((i.val-j.val-1 : ℕ) : ℝ)/2) ∧
          spectral (timeBlock i j DJ) ≤
            C0 * Real.sqrt δL * Real.exp (-δL*((i.val-j.val-1 : ℕ) : ℝ)/2)) ∧
        (∀ x y : Valid r m (CombinedPrivate n m aH a),
          DR x y ≠ 0 → y.val.1 ≤ x.val.1 ∧ x.val.2.1 = y.val.2.1) ∧
        (∀ x y : Valid r m (CombinedPrivate n m aH a),
          DJ x y ≠ 0 → addsJump x.val.1 y.val.1 x.val.2.1 y.val.2.1) := by sorry

end LindbladQueryOptimal.Simulation
