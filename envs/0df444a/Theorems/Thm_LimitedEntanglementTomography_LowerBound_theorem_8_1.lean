-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_theorem_8_1
-- name    : LimitedEntanglementTomography.LowerBound.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:15.933195+00:00
-- url     : https://prove2.me/theorems/6dd08558-4be7-405b-8f00-5f1d5e0feb0c
-- title:
--   Theorem 8.1 — Fisher information of a block measurement, eqs. (54)–(56)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $d\ge2$, $t\ge1$, and let $\rho$ be a state of full rank. Every POVM $M$ on $t$ copies (with any standard Borel outcome space) satisfies
--   $$\operatorname{tr}J_M(\rho)\le\min\Big\{\frac{2t^{3/2}}{\lambda_{\min}(\rho)^2},\ \frac{t(d^2-1)}{\lambda_{\min}(\rho)}\Big\}.$$
--   In particular, if $\rho\succeq I_d/(4d)$, then
--   $$\operatorname{tr}J_M(\rho)\le C\min\{d^2t^{3/2},\,d^3t\}=C\,d^2t\sqrt{\min\{t,d^2\}} .$$
--
--   Near the maximally mixed state the bound interpolates between the cost $d^2t^{3/2}$ of small blocks and the unrestricted $d^3t$; it is the per-round input of Proposition 7.1.
--
--   Differences from the source:
--   - encoding: ρ a state of full rank → WildeQIT.IsDensityOperator ρ together with ρ.PosDef; reason: a positive semidefinite matrix has full rank exactly when it is positive definite
--   - encoding: tr J = E‖s_θ‖² with the score of the density p_θ = tr(K R_θ) (§4.2) → supremum over measurable maps φ into finite sets of the Fisher information of φ(Y), with values in [0,∞] (povmFisherTrace / Protocol.fisherTrace); reason: equal to the source quantity by the source's own Fact 4.3, eq. (16); extended values exclude any junk zero, and a non-differentiable outcome probability counts as +∞
--   - encoding: one fixed Frobenius-orthonormal basis F_1,…,F_{d²−1} of Herm₀(ℂ^d) → the statement holds for every orthonormal basis F (IsHerm0ONB F); reason: the source fixes an arbitrary such basis, so its claim is the same claim for every basis; trace Fisher information and the standard Gaussian law do not depend on the basis
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §8, printed p.27 / PDF p.29, Theorem 8.1 (eqs. (54)–(56))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Measurement

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Theorem 8.1, printed p.27 / PDF p.29, eqs. (54)–(56).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Theorem 8.1.** There is an absolute constant `C > 0` such that for every `d ≥ 2`, `t ≥ 1`,
full-rank state `ρ`, and POVM `M` on `t` copies (any standard Borel outcome space):
(54) `tr J_M(ρ) ≤ min{2 t^{3/2} / λ_min(ρ)², t(d² − 1)/λ_min(ρ)}`; and if `ρ ⪰ I_d/(4d)` (55),
then (56) `tr J_M(ρ) ≤ C min{d² t^{3/2}, d³ t}`, where `min{d² t^{3/2}, d³ t} = d² t √(min{t, d²})`. -/
theorem theorem_8_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d → ∀ (t : ℕ), 1 ≤ t → ∀ (ρ : Op d),
      WildeQIT.IsDensityOperator ρ → ρ.PosDef →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (M : POVM (Fin t → Fin d) Ω)
        (F : Fin (d ^ 2 - 1) → Op d), IsHerm0ONB F →
        povmFisherTrace F M ρ ≤ ENNReal.ofReal (min (2 * (t : ℝ) ^ ((3 : ℝ) / 2) / lambdaMin ρ ^ 2)
          ((t : ℝ) * ((d : ℝ) ^ 2 - 1) / lambdaMin ρ)) ∧
        (LoewnerGE ρ (1 / (4 * (d : ℝ))) →
          povmFisherTrace F M ρ ≤ ENNReal.ofReal
            (C * min ((d : ℝ) ^ 2 * (t : ℝ) ^ ((3 : ℝ) / 2)) ((d : ℝ) ^ 3 * t))) ∧
        min ((d : ℝ) ^ 2 * (t : ℝ) ^ ((3 : ℝ) / 2)) ((d : ℝ) ^ 3 * t) =
          (d : ℝ) ^ 2 * t * Real.sqrt (min (t : ℝ) ((d : ℝ) ^ 2)) := by sorry

end LimitedEntanglementTomography.LowerBound
