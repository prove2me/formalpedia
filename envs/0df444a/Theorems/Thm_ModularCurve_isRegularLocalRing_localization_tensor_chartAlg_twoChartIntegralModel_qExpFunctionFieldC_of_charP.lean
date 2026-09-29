-- Prove2me | Theorems.Thm_ModularCurve_isRegularLocalRing_localization_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_of_charP
-- name    : ModularCurve.isRegularLocalRing_localization_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/e43f4603-d08f-5558-bbf7-dc90e2147008
-- title:
--   Igusa good reduction: regular one-dimensional charts at p ∤ M
-- statement:
--   Fix $M \ge 1$ and a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(M) \le \Gamma \le \Gamma_0(M)$, and a prime $p$ with $p \nmid M$. Let $F = \mathrm{qExpFunctionFieldC}(\mathbb{Q},\Gamma)$ be the intermediate field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ all quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ of $q$-expansions of modular forms of equal weight for $\Gamma$ having integral $q$-expansions $p_f, p_g$ (with the denominator series nonzero), and let $j \in F$ be nonzero with Laurent series equal to $\mathrm{jqModC}\,\mathbb{Q} = q^{-1}\cdot(E_4^3\,\eta^{-24})$, the $q$-expansion of the modular invariant. Let $\Lambda = \mathrm{GaloisRep.ratLocalizedAt}\,p$ be the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $p$, and let $k$ be an algebraically closed field of characteristic $p$ equipped with a $\Lambda$-algebra structure. Write $\mathcal{O}_{\mathrm{fin}} = \mathrm{chartAlgFin}$ and $\mathcal{O}_{\mathrm{inf}} = \mathrm{chartAlgInf}$ for the subalgebras of $F$ consisting of the elements integral over $\Lambda[j]$, respectively over $\Lambda[j^{-1}]$. The conclusion is the conjunction of two assertions: for every maximal ideal $\mathfrak{m}$ of $k \otimes_{\Lambda} \mathcal{O}_{\mathrm{fin}}$, the localisation at $\mathfrak{m}$ is a regular local ring of Krull dimension $1$ (as an element of $\mathbb{N}_\infty$), and the same holds for every maximal ideal of $k \otimes_{\Lambda} \mathcal{O}_{\mathrm{inf}}$.
--
--   This is the local form of Igusa's good-reduction theorem: the geometric fibre at a prime $p \nmid M$ of the Kroneckerian model of the modular curve attached to $\Gamma$, presented by the two affine charts given by the integral closures of $\Lambda[j]$ and $\Lambda[j^{-1}]$, has regular local rings of dimension one. It feeds the smoothness of relative dimension one of the special fibre of the two-chart integral model, [`ModularCurve.smoothOfRelativeDimension_one_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP`](thm.html#ModularCurve.smoothOfRelativeDimension_one_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isRegularLocalRing_localization_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups TensorProduct
open AlgebraicCurve
open ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.isRegularLocalRing_localization_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_of_charP
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [Algebra ↥(GaloisRep.ratLocalizedAt p) k] :
    (∀ (m : Ideal (k ⊗[↥(GaloisRep.ratLocalizedAt p)]
        ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))) (_ : m.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = (1 : ℕ∞)) ∧
    (∀ (m : Ideal (k ⊗[↥(GaloisRep.ratLocalizedAt p)]
        ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))) (_ : m.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = (1 : ℕ∞)) := by sorry
