-- Prove2me | Theorems.Thm_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S
-- name    : ModularCurve.apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/e1484e54-fb3a-5503-98d2-464c3930d0a7
-- title:
--   Cusp-0 expansion sends ̄ j(qᵈ) to ̄ j(q^N)
-- statement:
--   Fix a nonzero natural number $M$, a prime $\ell$ with $\ell \nmid M$, and an algebraically closed field $K$ of characteristic $\ell$, together with a ring homomorphism $\varphi$ from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ to $K$, and nonzero natural numbers $N, d$ with $N d = M$. Let $\Gamma =$ [`CohCarrier.GammaH M ⊥`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained by pulling back the trivial subgroup of $(\mathbb{Z}/M)^\times$ along the character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$, $\gamma \mapsto \gamma_{2,2} \bmod M$, and pushing forward along the inclusion of $\Gamma_0(M)$. The field [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) is the intermediate field of $K((q))$ generated over $K$ by the quotients $\overline{p_f}/\overline{p_g}$, where $f, g$ are modular forms of some weight $k$ for $\Gamma$ (regarded in $\mathrm{GL}(2,\mathbb{R})$), $p_f, p_g$ are integral power series whose images in $\mathbb{C}[[q]]$ are the width-one $q$-expansions of $f$ and $g$, $\overline{p_g} \neq 0$, and bars denote reduction of coefficients to $K$. Let $\Theta$ be a $K$-algebra homomorphism from this field to $K((q))$ satisfying the following pinning hypothesis $h\Theta$: whenever $k \in \mathbb{Z}$, $f, h$ are weight-$k$ forms for $\Gamma$ with integral expansions $p_f, p_h$ and $\overline{p_h} \neq 0$, $a \in \mathbb{N}$, and $F, G$ are power series over the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ whose images in $\mathbb{C}[[q]]$ are $M^a \cdot$ the width-$M$ $q$-expansions of $f \mid_k S$ and $h \mid_k S$ respectively ($S$ the standard order-four generator of $\mathrm{SL}(2,\mathbb{Z})$), then for every $x$ in the field with Laurent series $\overline{p_f}/\overline{p_h}$ one has $\varphi_*G \neq 0$ in $K((q))$ and $\Theta x = \varphi_*F / \varphi_*G$. The conclusion: for every $x$ in [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) whose underlying Laurent series is [`ModularCurve.qExpand K d (ModularCurve.jqModC K)`](def/ModularCurve_X0.html#L25), i.e. the series $q^{-1} E_4^3 \eta^{-24}$ reduced to $K$ with $q$ replaced by $q^d$, one has $\Theta x =$ the same series with $q$ replaced by $q^N$.
--
--   This records, in the frame of a cusp expansion at $0 = S\infty$ for level $M = Nd$ in characteristic $\ell \nmid M$, the classical Fricke-involution identity $j(d \cdot (-1/(M\tau))) = j(N\tau)$, in the reduced form $\bar j(q^d) \mapsto \bar j(q^N)$. It is used, together with the companion statement on periods, to show that $\bar j(q^N)$ does not lie in the mod-$\ell$ $q$-expansion function field of level $M$ attached to [`CohCarrier.GammaH M ⊥`](def/CohCarrier_Level.html#L133).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S
    (M : ℕ) [NeZero M] {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (φ : integralClosure ℤ ℂ →+* K)
    (N d : ℕ) [NeZero N] [NeZero d] (hM : N * d = M)
    (Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] LaurentSeries K)
    (hΘ :
      ∀ (k : ℤ) (f h : ModularForm (CohCarrier.GammaH M ⊥ : Subgroup (GL (Fin 2) ℝ)) k)
        (pf ph : PowerSeries ℤ), ModularCurve.IsIntegralQExp f pf →
        ModularCurve.IsIntegralQExp h ph → ModularCurve.intSeriesC K ph ≠ 0 →
        ∀ (a : ℕ) (F G : PowerSeries (integralClosure ℤ ℂ)),
          F.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularGroup.S) →
          G.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑h : UpperHalfPlane → ℂ) ∣[k] ModularGroup.S) →
          ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K ph →
            HahnSeries.ofPowerSeries ℤ K (G.map φ) ≠ 0 ∧
              (Θ x : LaurentSeries K) =
                HahnSeries.ofPowerSeries ℤ K (F.map φ) / HahnSeries.ofPowerSeries ℤ K (G.map φ)) :
    ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
      (x : LaurentSeries K) = ModularCurve.qExpand K d (ModularCurve.jqModC K) →
        (Θ x : LaurentSeries K) = ModularCurve.qExpand K N (ModularCurve.jqModC K) := by sorry
