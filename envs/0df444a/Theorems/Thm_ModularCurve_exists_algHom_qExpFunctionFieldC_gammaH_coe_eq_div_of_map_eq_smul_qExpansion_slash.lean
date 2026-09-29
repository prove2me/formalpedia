-- Prove2me | Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash
-- name    : ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/84985593-c02d-541b-a9b5-ecadbad717b4
-- title:
--   Mod ℓ q-expansion principle at an arbitrary cusp of X_H(M)
-- statement:
--   Let $M\ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $\Gamma_H(M)\le \mathrm{SL}(2,\mathbb{Z})$ be [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}(2,\mathbb{Z})$ of the set of $\gamma\in\Gamma_0(M)$ whose associated unit $\bar d\in(\mathbb{Z}/M)^\times$ lies in $H$. Let $\ell$ be a prime not dividing $M$, let $K$ be an algebraically closed field of characteristic $\ell$, let $\varphi$ be a ring homomorphism from the integral closure $\overline{\mathbb{Z}}$ of $\mathbb{Z}$ in $\mathbb{C}$ to $K$, and let $g\in\mathrm{SL}(2,\mathbb{Z})$. Write $\mathcal{F}=$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)`](def/ModularCurve_X1.html#L101) for the intermediate field of $K((q))$ generated over $K$ by all quotients $\overline{p_f}/\overline{p_h}$, where $f,h$ are modular forms of some common weight on $\Gamma_H(M)$ (as a subgroup of $\mathrm{GL}(2,\mathbb{R})$), $p_f,p_h$ are power series over $\mathbb{Z}$ whose images in $\mathbb{C}[[q]]$ are the $q$-expansions of $f$ and $h$ at $\infty$ (with $q=e^{2\pi i\tau}$), $\overline{\,\cdot\,}$ denotes coefficientwise reduction along $\mathbb{Z}\to K$ viewed in $K((q))$, and $\overline{p_h}\ne 0$. The assertion is that there exists a $K$-algebra homomorphism $\Theta:\mathcal{F}\to K((q))$ such that for every weight $k\in\mathbb{Z}$, all modular forms $f,h$ of weight $k$ on $\Gamma_H(M)$, all $p_f,p_h\in\mathbb{Z}[[q]]$ representing their integral $q$-expansions at $\infty$ with $\overline{p_h}\ne0$, every $a\in\mathbb{N}$ and all power series $F,G$ over $\overline{\mathbb{Z}}$ whose images in $\mathbb{C}[[q_M]]$ equal $M^a$ times the $q_M$-expansions ($q_M=e^{2\pi i\tau/M}$) of $f\mid_k g$ and $h\mid_k g$ respectively, and every $x\in\mathcal{F}$ whose underlying Laurent series is $\overline{p_f}/\overline{p_h}$: the Laurent series attached to $\varphi(G)\in K[[q]]$ is non-zero, and $\Theta x=\varphi(F)/\varphi(G)$ in $K((q))$.
--
--   This is the $q$-expansion principle modulo $\ell$ at the cusp $g\infty$: reducing the expansions at $g\infty$ along $\varphi$ is well defined and multiplicative on the function field of $X_H(M)$ in characteristic $\ell$, the case $g=1$ recovering the tautological inclusion into $K((q))$. It is the input at the cusps for the comparison of $q$-expansions at different cusps used in the diamond-operator and $q$-twist computations on $X_H(M)$ modulo $\ell$, and in showing that $j$ does not lie in the corresponding function field at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash.lean

import Mathlib
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (φ : integralClosure ℤ ℂ →+* K) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] LaurentSeries K,
      ∀ (k : ℤ) (f h : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf ph : PowerSeries ℤ), ModularCurve.IsIntegralQExp f pf →
        ModularCurve.IsIntegralQExp h ph → ModularCurve.intSeriesC K ph ≠ 0 →
        ∀ (a : ℕ) (F G : PowerSeries (integralClosure ℤ ℂ)),
          F.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑f : UpperHalfPlane → ℂ) ∣[k] g) →
          G.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑h : UpperHalfPlane → ℂ) ∣[k] g) →
          ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K ph →
            HahnSeries.ofPowerSeries ℤ K (G.map φ) ≠ 0 ∧
              (Θ x : LaurentSeries K) =
                HahnSeries.ofPowerSeries ℤ K (F.map φ) / HahnSeries.ofPowerSeries ℤ K (G.map φ) := by sorry
