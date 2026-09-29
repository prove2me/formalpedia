-- Prove2me | Theorems.Thm_ModularCurve_diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
-- name    : ModularCurve.diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/ad791066-588e-5b27-90b9-8db555693cd6
-- title:
--   φ-linearity of the q-expansion pin of ρ^∞
-- statement:
--   Let $p$ be prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$, and let $K$ be a field of characteristic $p$ equipped with its $\mathbb{Z}/p$-algebra structure. Write $\Gamma_H(M)$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ given by the lower-right entry mod $M$, and let $\Gamma_{H'}(M/p)$ be the corresponding group for the image $H'$ of $H$ in $(\mathbb{Z}/(M/p))^\times$. Let $F =$ `qExpFunctionFieldC K`$\,\Gamma_{H'}(M/p)$ be the intermediate field of $K((q))$ generated over $K$ by the $q$-expansions of the ratios `intFormRatiosC`, and let $\Theta =$ `diffQExp`$\,F \colon \Omega[F/K] \to K((q))$ be the $F$-linear map obtained by lifting the derivation $q\,d/dq$ restricted to $F$. Let $\rho^\infty \colon K \otimes_{\mathbb{Z}/p} \mathrm{IntTwoCuspForms}(M,H,p) \to \Omega[F/K]$ be $K$-linear and satisfy `IsInfReductionMap`: for every weight-$2$ cusp form $f$ on $\Gamma_H(M)$ lying in the two-cusp integrality set — that is, such that for every $t$ in the Hecke ring `heckeRingH M H 2`, every Atkin–Lehner datum $W$ at $p$ and every $n$, the $n$-th $q$-coefficients of $t f$ and of the Atkin–Lehner slash `alSlash W 2` of $t f$ lie in the trivial subring $\bot \subseteq \mathbb{C}$ — and every $P_f \in \mathbb{Z}[[q]]$ with `IsIntegralQExp f`$\,P_f$, one has $\Theta(\rho^\infty(1 \otimes \overline{f})) =$ `intSeriesC K`$\,P_f$, where $\overline{f}$ denotes the class of $f$ under `intTwoCuspReduce`, the quotient map from the $\bot$-span `twoCuspLattice` of that integrality set to its quotient by `intIdeal p` $\cdot\ \top$. Let $\varphi$ be a ring homomorphism from the integral closure $\overline{\mathbb{Z}}$ of $\mathbb{Z}$ in $\mathbb{C}$ to $K$, let $a \colon \mathrm{Fin}\,n \to \overline{\mathbb{Z}}$, and let $f \colon \mathrm{Fin}\,n \to$ weight-$2$ cusp forms on $\Gamma_H(M)$, each lying in the above integrality set. Finally let $pg \in \overline{\mathbb{Z}}[[q]]$ be a power series whose image in $\mathbb{C}[[q]]$ is the width-$1$ $q$-expansion of $\sum_i (a_i : \mathbb{C}) \cdot f_i$. Then $$\Theta\Bigl(\sum_i \varphi(a_i)\,\rho^\infty\bigl(1 \otimes \overline{f_i}\bigr)\Bigr) = \mathrm{ofPowerSeries}\bigl(\varphi_*(pg)\bigr),$$ the Laurent series over $K$ attached to the coefficientwise image of $pg$ under $\varphi$.
--
--   This is the $q$-expansion pin for an $\infty$-reduction map, extended $\varphi$-linearly from $\mathbb{Z}$-integral weight-$2$ forms to $\overline{\mathbb{Z}}$-linear combinations of two-cusp integral forms, the combinations being given explicitly so that no tensor-product generators need be manipulated. It is used in the Atkin–Lehner pinning arguments on differentials of $X_{H'}(M/p)$, for instance in [`ModularCurve.bijective_of_atkinLehnerPinAlong`](thm.html#ModularCurve.bijective_of_atkinLehnerPinAlong) and in the recognition of regular differentials under such a pin.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (K : Type*) [Field K] [CharP K p] [Algebra (ZMod p) K]
    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (φ : ↥(integralClosure ℤ ℂ) →+* K)
    {n : ℕ} (a : Fin n → ↥(integralClosure ℤ ℂ)) (f : Fin n → CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ i, f i ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pg : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpg : pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 (⇑(∑ i, ((a i : ℂ)) • f i))) :
    ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        (∑ i, φ (a i) • ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨f i, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (hf i)⟩)) =
      HahnSeries.ofPowerSeries ℤ K (pg.map φ) := by sorry
