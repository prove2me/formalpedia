-- Prove2me | Theorems.Thm_ModularCurve_IsInfReductionMap_smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke
-- name    : ModularCurve.IsInfReductionMap.smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/22e69fd1-a4c7-5eef-8f6c-73d2b157175b
-- title:
--   q-expansion of the Fricke pullback of ρ^∞(̄ f)
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$ but $p^2\nmid M$, and a subgroup $H\le(\mathbb Z/M)^\times$ containing the kernel of the reduction $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$ (stated as: every unit mapping to $1$ lies in $H$), with $M/p\neq 0$. Let $K$ be an algebraically closed field of characteristic $p$, and write $H'=$ [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246) for the image of $H$ in $(\mathbb Z/(M/p))^\times$ and $\bar F=$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M/p) H')`](def/ModularCurve_X1.html#L101) for the subfield of $K((q))^{\mathrm{Laurent}}$ generated over $K$ by the integral form ratios attached to $\Gamma_{H'}(M/p)$. Let $\rho^\infty\colon K\otimes_{\mathbb Z/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) $\to\Omega[\bar F\!\;/K]$ be $K$-linear and satisfy `IsInfReductionMap`, i.e. for every weight-two cusp form $f$ on $\Gamma_H(M)$ in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54) (all $q$-coefficients of $tf$ and of $tf\mid_2 W$ lie in the prime subring of $\mathbb C$, for all Hecke operators $t$ in `heckeRingH` and all Atkin–Lehner data $W$ at $(M,p)$) and every $P_f\in\mathbb Z[[q]]$ whose image in $\mathbb C[[q]]$ is the $q$-expansion of $f$, the $q$-expansion `diffQExp` of $\rho^\infty(1\otimes\bar f)$ is the image of $P_f$ in $K((q))$. Further data: an Atkin–Lehner datum $W_d$ at $(M,M/p)$ (an $R$ with $M=(M/p)R$ and integers $a,b$ with $(M/p)a-Rb=1$); a unit $e\in(\mathbb Z/M)^\times$ whose image in $\mathbb Z/(M/p)$ satisfies $\bar e\,\bar p=1$; a ring homomorphism $\varphi$ from the algebraic integers in $\mathbb C$ to $K$; an element $W_Q\in\mathrm{GL}_2(\mathbb R)$ with matrix $\begin{pmatrix}0&-1\\M/p&0\end{pmatrix}$; and a $K$-algebra automorphism $\sigma$ of $\bar F$ subject to the hypothesis $h\sigma$: whenever $f,g$ are modular forms of weight $k$ on $\Gamma_{H'}(M/p)$ with integral $q$-expansion series $p_f,p_g\in\mathbb Z[[q]]$, $D\in\mathbb N$, and $P_f^W,P_g^W$ are series over the algebraic integers whose images in $\mathbb C[[q]]$ are the $q$-expansions of $D\,(f\mid_k W_Q)$ and $D\,(g\mid_k W_Q)$, and both the image of $p_g$ in $K((q))$ and $\varphi(P_g^W)$ are nonzero, then every $x\in\bar F$ whose Laurent series is the ratio of the images of $p_f$ and $p_g$ satisfies $\sigma(x)\cdot\varphi(P_g^W)=\varphi(P_f^W)$. Then, for every weight-two cusp form $f$ on $\Gamma_H(M)$ in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54), every $D\in\mathbb N$ with $p\nmid D$, and every series $P^W_f$ over the algebraic integers whose image in $\mathbb C[[q]]$ is the $q$-expansion of $D\cdot\big(\langle e\rangle f\big)\mid_2 W_d$ (with $\langle e\rangle=$ [`CuspForm.diamondLinH 2 e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132)), one has $$D\cdot\mathrm{diffQExp}\big(\sigma^{*}\rho^\infty(1\otimes\overline{f})\big)=\varphi(P^W_f)$$ in $K((q))$, where $\sigma^{*}$ is [`AlgebraicCurve.Differential.pullbackAlong`](def/AlgebraicCurve_DifferentialPushPull.html#L16) applied to $\sigma$ and $\bar f$ denotes [`CuspForm.intTwoCuspReduce`](def/ModularCurve_XHDifferentialsModL.html#L401) of $f$.
--
--   This is the geometric clause of the Fricke-pair statement for the component $\Sigma^\infty$ of the mod-$p$ fibre, isolated as a $q$-expansion identity: the Atkin–Lehner involution $w_{M/p}$ of $X_H(M)$, given on weight-two forms by $f\mapsto(\langle e\rangle f)\mid_2 W_d$, preserves that component and acts there through the automorphism $\sigma$ of its function field. It is used in the construction of a pair of algebra automorphisms intertwining the two mod-$\ell$ Hecke operators on the reduction, en route to level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsInfReductionMap_smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups ModularForm

theorem ModularCurve.IsInfReductionMap.smul_diffQExp_pullbackAlong_eq_ofPowerSeries_map_of_reduction_slash_fricke
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (φ : ↥(integralClosure ℤ ℂ) →+* K)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    (σ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
    (hσ : ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map φ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((σ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) :
                  LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map φ) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map φ))
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (D : ℕ) (hD : ¬ p ∣ D)
    (pfW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpfW : pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))) :
    (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        (AlgebraicCurve.Differential.pullbackAlong
          σ.toAlgHom
          (ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩))) =
      HahnSeries.ofPowerSeries ℤ K (pfW.map φ) := by sorry
