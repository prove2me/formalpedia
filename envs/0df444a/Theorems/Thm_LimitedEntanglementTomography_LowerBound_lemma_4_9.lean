-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_lemma_4_9
-- name    : LimitedEntanglementTomography.LowerBound.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:34.402772+00:00
-- url     : https://prove2.me/theorems/391a294e-8c5e-488e-be43-17b632ee0274
-- title:
--   Lemma 4.9 — scores of rank-one block measurements, eqs. (24)–(25)
-- statement:
--   Let $\rho$ be a state of full rank, $R=\rho^{\otimes t}$ with $t\ge1$, and let $M=\{w_z|v_z\rangle\langle v_z|\}_z$ be a finite POVM whose effects have rank one, with $w_z>0$ and $\|v_z\|_2=1$. Define
--   $$q_z=\langle v_z|R|v_z\rangle,\qquad p_z=w_zq_z,\qquad |u_z\rangle=\frac{R^{1/2}|v_z\rangle}{\sqrt{q_z}},\qquad H_b=\rho^{-1/2}F_b\rho^{-1/2}.$$
--   Then $p_z=\operatorname{tr}(M_zR)$ is the probability of outcome $z$, and its score $s_b(z)=\partial_{\theta_b}\log p_z(\theta)|_{\theta=0}$, where $p_z(\theta)=w_z\langle v_z|(\rho+\sum_c\theta_cF_c)^{\otimes t}|v_z\rangle$, satisfies
--   $$s_b(z)=\operatorname{tr}\big(H_bG_1(u_z)\big)=\operatorname{tr}\big(H_b(G_1(u_z)-t\rho)\big).$$
--   The same vectors satisfy
--   $$\sum_zp_z|u_z\rangle\langle u_z|=\rho^{\otimes t},\qquad\sum_zp_zG_1(u_z)=t\rho .$$
--
--   These identities express the score of a block measurement through the unfolded matrix, the starting point of Theorem 8.1.
--
--   Differences from the source:
--   - encoding: ρ a state of full rank → WildeQIT.IsDensityOperator ρ together with ρ.PosDef; reason: a positive semidefinite matrix has full rank exactly when it is positive definite
--   - encoding: s_b(z) = tr(H_b G₁(u_z)) as real numbers → the real score, cast to ℂ, equals the complex trace tr(H_b G₁(u_z)); reason: H_b and G₁(u_z) are Hermitian, so the trace is real; the complex equation is the source equation
--   - encoding: the partial derivative in θ_b of log p_z(θ) → the derivative at 0 of s ↦ log p_z along the line ρ + s F_b; reason: the partial derivative in coordinate b is the derivative along F_b
--   - encoding: one fixed Frobenius-orthonormal basis F_1,…,F_{d²−1} of Herm₀(ℂ^d) → the statement holds for every orthonormal basis F (IsHerm0ONB F); reason: the source fixes an arbitrary such basis, so its claim is the same claim for every basis; trace Fisher information and the standard Gaussian law do not depend on the basis
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §4.3, printed p.14 / PDF p.16, Lemma 4.9 (eqs. (24)–(25))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Matrices

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Lemma 4.9, printed p.14 / PDF p.16, eqs. (24)–(25).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Lemma 4.9.** Let `ρ` be a full-rank state, `R = ρ^{⊗t}`, and `M = {w_z |v_z⟩⟨v_z|}_z` a finite
POVM with rank-one effects (`w_z > 0`, `‖v_z‖₂ = 1`). With `q_z = ⟨v_z|R|v_z⟩`, `p_z = w_z q_z`,
`|u_z⟩ = R^{1/2}|v_z⟩/√q_z` and `H_b = ρ^{-1/2} F_b ρ^{-1/2}`: `p_z` is the probability
`tr(M_z R)` of outcome `z`; its score `s_b(z) = ∂_{θ_b} log p_z(ρ + ∑ θ_c F_c)|_{θ=0}` satisfies
`s_b(z) = tr(H_b G₁(u_z)) = tr(H_b (G₁(u_z) − tρ))` (24); and `∑_z p_z |u_z⟩⟨u_z| = ρ^{⊗t}`,
`∑_z p_z G₁(u_z) = tρ` (25). -/
theorem lemma_4_9 (d t : ℕ) (ht : 1 ≤ t) (ρ : Op d) (hρ : WildeQIT.IsDensityOperator ρ)
    (hfull : ρ.PosDef) {Z : Type} [Fintype Z] (w : Z → ℝ) (v : Z → (Fin t → Fin d) → ℂ)
    (hw : ∀ z, 0 < w z) (hv : ∀ z, star (v z) ⬝ᵥ v z = 1)
    (hM : ∑ z, ((w z : ℝ) : ℂ) • vecMulVec (v z) (star (v z)) = 1)
    (F : Fin (d ^ 2 - 1) → Op d) (hF : IsHerm0ONB F) :
    let R := tensorPow ρ t
    let q : Z → ℝ := fun z => (star (v z) ⬝ᵥ (R *ᵥ v z)).re
    let p : Z → ℝ := fun z => w z * q z
    let u : Z → (Fin t → Fin d) → ℂ := fun z => (((Real.sqrt (q z))⁻¹ : ℝ) : ℂ) • (psdSqrt R *ᵥ v z)
    let H : Fin (d ^ 2 - 1) → Op d := fun b => invSqrt ρ * F b * invSqrt ρ
    let s : Fin (d ^ 2 - 1) → Z → ℝ := fun b z =>
      deriv (fun θ : ℝ => Real.log (w z *
        (star (v z) ⬝ᵥ (tensorPow (ρ + ((θ : ℝ) : ℂ) • F b) t *ᵥ v z)).re)) 0
    (∀ z, p z = (trace ((((w z : ℝ) : ℂ) • vecMulVec (v z) (star (v z))) * R)).re) ∧
    (∀ b z, ((s b z : ℝ) : ℂ) = trace (H b * unfolded (u z)) ∧
      trace (H b * unfolded (u z)) = trace (H b * (unfolded (u z) - ((t : ℝ) : ℂ) • ρ))) ∧
    ∑ z, ((p z : ℝ) : ℂ) • vecMulVec (u z) (star (u z)) = R ∧
    ∑ z, ((p z : ℝ) : ℂ) • unfolded (u z) = ((t : ℝ) : ℂ) • ρ := by sorry

end LimitedEntanglementTomography.LowerBound
