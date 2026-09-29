-- Prove2me | Theorems.Thm_ModularCurve_eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash
-- name    : ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/017194c0-1020-541b-abd4-455d4ed68906
-- title:
--   Joint injectivity of two reduction maps on mod-p two-cusp forms
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbf Z/M)^\times$ containing every unit whose image under the reduction $(\mathbf Z/M)^\times \to (\mathbf Z/(M/p))^\times$ is trivial. Let $K$ be an algebraically closed field of characteristic $p$, viewed as a $\mathbf Z/p$-algebra, let $W$ be an Atkin–Lehner datum for $(M,p)$ (an integer $R$ with $M = pR$ together with integers $a,b$ satisfying $pa - Rb = 1$), and let $e \in (\mathbf Z/M)^\times$ have image $\bar e$ in $\mathbf Z/(M/p)$ with $\bar e \cdot p = 1$. Let $\rho^{\infty}, \rho^{0}$ be $K$-linear maps from $K \otimes_{\mathbf Z/p} \mathtt{IntTwoCuspForms}\,M\,H\,p$ to the Kähler differentials $\Omega$ of the field [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))`](def/ModularCurve_X1.html#L101) over $K$, where the level group is $\Gamma_{H'}(M/p)$ for $H'$ the image of $H$ in $(\mathbf Z/(M/p))^\times$. Assume [`ModularCurve.IsInfReductionMap K p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L443) holds for $\rho^{\infty}$: for every weight-two cusp form $f$ on $\Gamma_H(M)$ in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54) (all $q$-coefficients of $tf$ and of $f \mid_2 W'$ for $t$ in the Hecke ring and any Atkin–Lehner datum $W'$ lie in the minimal subring of $\mathbf C$) and every $p_f \in \mathbf Z[[q]]$ whose complex image is the $q$-expansion of $f$, the differential $\rho^{\infty}(1 \otimes \bar f)$ has $q$-expansion `diffQExp` equal to the image of $p_f$ in $K[[q]] \subseteq$ the Laurent series over $K$; here $\bar f$ is the class of $f$ under [`CuspForm.intTwoCuspReduce`](def/ModularCurve_XHDifferentialsModL.html#L401). Assume the same condition for $\rho^{0}$, with $p_f$ instead an integral power series lifting the $q$-expansion of $(\langle e\rangle f) \mid_2 W$, i.e. of [`ModularForm.alSlash W 2 (CuspForm.diamondLinH 2 e f)`](def/ModularForm_AtkinLehnerDatum.html#L141). Then any $x$ in $K \otimes_{\mathbf Z/p} \mathtt{IntTwoCuspForms}\,M\,H\,p$ with $\rho^{\infty} x = 0$ and $\rho^{0} x = 0$ vanishes.
--
--   This is the $q$-expansion principle at the two cusps for weight-two forms of level $M$ with $p \parallel M$: the pair of reduction maps at the cusps $\infty$ and $0$ is jointly injective on the mod-$p$ two-cusp forms. It is used in the comparison of $K \otimes \mathtt{IntTwoCuspForms}$ with the regular differentials on the two components of the reduction, both for the dimension count and for the resulting linear isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (W : ModularForm.AtkinLehnerDatum M p)
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (ρinf ρzero : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hzero : (∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (pfW : PowerSeries ℤ), ModularCurve.IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW →
            ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
                (ρzero ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) =
              ModularCurve.intSeriesC K pfW))
    (x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p) (hx : ρinf x = 0) (hx' : ρzero x = 0) : x = 0 := by sorry
