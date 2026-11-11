-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_corollary_4_7
-- name    : LimitedEntanglementTomography.LowerBound.corollary_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:14.86244+00:00
-- url     : https://prove2.me/theorems/9953b8b3-1674-41b3-8a14-39697badaa38
-- title:
--   Corollary 4.7 — $\operatorname{tr} J_M(\rho)\le t(d^2-1)/\lambda_{\min}(\rho)$
-- statement:
--   Let $d\ge2$, let $\rho$ be a $d$-dimensional state of full rank, and let $t\ge1$. Every POVM $M$ on $t$ copies (with any standard Borel outcome space) satisfies
--   $$\operatorname{tr}J_M(\rho)\le\frac{t\,(d^2-1)}{\lambda_{\min}(\rho)} .$$
--
--   This is the bound obtained from the symmetric logarithmic derivative; it is the second term of (54) in Theorem 8.1 and the right bound for large blocks.
--
--   Differences from the source:
--   - encoding: ρ a state of full rank → WildeQIT.IsDensityOperator ρ together with ρ.PosDef; reason: a positive semidefinite matrix has full rank exactly when it is positive definite
--   - encoding: tr J = E‖s_θ‖² with the score of the density p_θ = tr(K R_θ) (§4.2) → supremum over measurable maps φ into finite sets of the Fisher information of φ(Y), with values in [0,∞] (povmFisherTrace / Protocol.fisherTrace); reason: equal to the source quantity by the source's own Fact 4.3, eq. (16); extended values exclude any junk zero, and a non-differentiable outcome probability counts as +∞
--   - encoding: one fixed Frobenius-orthonormal basis F_1,…,F_{d²−1} of Herm₀(ℂ^d) → the statement holds for every orthonormal basis F (IsHerm0ONB F); reason: the source fixes an arbitrary such basis, so its claim is the same claim for every basis; trace Fisher information and the standard Gaussian law do not depend on the basis
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §4.2, printed p.13 / PDF p.15, Corollary 4.7

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Measurement

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Corollary 4.7, printed p.13 / PDF p.15.
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Corollary 4.7.** Let `d ≥ 2`, let `ρ` be a full-rank state and `t ≥ 1`. Every POVM `M` on
`t` copies, with any standard Borel outcome space, satisfies
`tr J_M(ρ) ≤ t (d² − 1) / λ_min(ρ)` (Fisher information in the coordinates of any orthonormal
basis of `Herm₀(ℂ^d)`). -/
theorem corollary_4_7 (d : ℕ) (hd : 2 ≤ d) (ρ : Op d) (hρ : WildeQIT.IsDensityOperator ρ)
    (hfull : ρ.PosDef) (t : ℕ) (ht : 1 ≤ t) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (M : POVM (Fin t → Fin d) Ω) (F : Fin (d ^ 2 - 1) → Op d) (hF : IsHerm0ONB F) :
    povmFisherTrace F M ρ ≤ ENNReal.ofReal ((t : ℝ) * ((d : ℝ) ^ 2 - 1) / lambdaMin ρ) := by sorry

end LimitedEntanglementTomography.LowerBound
