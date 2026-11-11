-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_lemma_8_2
-- name    : LimitedEntanglementTomography.LowerBound.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:31.43393+00:00
-- url     : https://prove2.me/theorems/ab525a49-0643-4862-85ec-a8df533e53ed
-- title:
--   Lemma 8.2 — $\sum_z p_z\|G_1(u_z)-t\rho\|_F^2\le 2t^{3/2}$
-- statement:
--   Let $\rho$ be a state of full rank, $t\ge1$, and $M=\{w_z|v_z\rangle\langle v_z|\}_z$ a finite POVM on $t$ copies with rank-one effects ($w_z>0$, $\|v_z\|_2=1$). With the outcome probabilities $p_z=w_z\langle v_z|\rho^{\otimes t}|v_z\rangle$ and vectors $u_z=(\rho^{\otimes t})^{1/2}v_z/\sqrt{\langle v_z|\rho^{\otimes t}|v_z\rangle}$ of Lemma 4.9,
--   $$\sum_zp_z\,\|G_1(u_z)-t\rho\|_F^2\le2\,t^{3/2}.$$
--
--   The average squared deviation is smaller than the pointwise bound $t^2$ by a factor $\sqrt t$; this gives the $t^{3/2}$ term of Theorem 8.1.
--
--   Differences from the source:
--   - encoding: ρ a state of full rank → WildeQIT.IsDensityOperator ρ together with ρ.PosDef; reason: a positive semidefinite matrix has full rank exactly when it is positive definite
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §8, printed p.27 / PDF p.29, Lemma 8.2 (eq. (57))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Matrices

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Lemma 8.2, printed p.27 / PDF p.29, eq. (57).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Lemma 8.2.** In the setting of Lemma 4.9 (full-rank state `ρ`, finite rank-one POVM
`{w_z |v_z⟩⟨v_z|}` on `t` copies, `p_z = w_z ⟨v_z|ρ^{⊗t}|v_z⟩`,
`u_z = (ρ^{⊗t})^{1/2} v_z / √⟨v_z|ρ^{⊗t}|v_z⟩`):
`∑_z p_z ‖G₁(u_z) − tρ‖_F² ≤ 2 t^{3/2}`. -/
theorem lemma_8_2 (d t : ℕ) (ht : 1 ≤ t) (ρ : Op d) (hρ : WildeQIT.IsDensityOperator ρ)
    (hfull : ρ.PosDef) {Z : Type} [Fintype Z] (w : Z → ℝ) (v : Z → (Fin t → Fin d) → ℂ)
    (hw : ∀ z, 0 < w z) (hv : ∀ z, star (v z) ⬝ᵥ v z = 1)
    (hM : ∑ z, ((w z : ℝ) : ℂ) • vecMulVec (v z) (star (v z)) = 1) :
    let R := tensorPow ρ t
    let q : Z → ℝ := fun z => (star (v z) ⬝ᵥ (R *ᵥ v z)).re
    let p : Z → ℝ := fun z => w z * q z
    let u : Z → (Fin t → Fin d) → ℂ := fun z => (((Real.sqrt (q z))⁻¹ : ℝ) : ℂ) • (psdSqrt R *ᵥ v z)
    ∑ z, p z * frobNorm (unfolded (u z) - ((t : ℝ) : ℂ) • ρ) ^ 2 ≤ 2 * (t : ℝ) ^ ((3 : ℝ) / 2) := by sorry

end LimitedEntanglementTomography.LowerBound
