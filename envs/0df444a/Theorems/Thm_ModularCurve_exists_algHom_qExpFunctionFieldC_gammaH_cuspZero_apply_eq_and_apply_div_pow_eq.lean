-- Prove2me | Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq
-- name    : ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/4ec6c982-0a95-5e9a-a684-d5953d17c8bd
-- title:
--   Expansion at the cusp 0 for X_H(M) in characteristic ℓ
-- statement:
--   Let $M \ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, let $\ell$ be a prime with $\ell \nmid M$, and let $K$ be an algebraically closed field of characteristic $\ell$. Write $\Gamma_H(M) =$ [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image under the inclusion of $\Gamma_0(M)$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ given by the lower-right entry modulo $M$, and let $\bar F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)`](def/ModularCurve_X1.html#L101) be the intermediate field of the Laurent series field `LaurentSeries K` obtained by adjoining to $K$ all quotients $\bar p_f/\bar p_h$, where $f, h$ are modular forms of one and the same weight $k \in \mathbb{Z}$ for $\Gamma_H(M)$ viewed inside $\mathrm{GL}_2(\mathbb{R})$, $p_f, p_h \in \mathbb{Z}[[q]]$ are power series whose images in $\mathbb{C}[[q]]$ are the width-one $q$-expansions of $f$ and $h$ (the predicate [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37)), $\bar{\;\cdot\;}$ denotes the induced Laurent series over $K$ ([`ModularCurve.intSeriesC`](def/ModularCurve_X1.html#L69)), and $\bar p_h \neq 0$. The assertion is the existence of a $K$-algebra homomorphism $\Theta \colon \bar F \to$ `LaurentSeries K` with three properties. First, every $x \in \bar F$ whose underlying Laurent series is [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the reduction to $K$ of the integral power series $E_4^3 \cdot \eta$-unit-inverse, satisfies $\Theta(x) =$ [`ModularCurve.jqNModC K M`](def/ModularCurve_JqCoeff.html#L18), the image of that series under the substitution $q \mapsto q^M$ ([`ModularCurve.qExpand K M`](def/ModularCurve_X0.html#L25)). Second, every $x \in \bar F$ whose underlying Laurent series is [`ModularCurve.jqNModC K M`](def/ModularCurve_JqCoeff.html#L18) satisfies $\Theta(x) =$ [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15). Third, for every $k \in \mathbb{Z}$, every modular form $f$ of weight $k$ for $\Gamma_H(M)$ and every $p_f \in \mathbb{Z}[[q]]$ with `IsIntegralQExp f pf` and $\bar p_f \neq 0$, there is a non-zero $y \in$ `LaurentSeries K` such that for all $n \in \mathbb{N}$, all modular forms $F$ of weight $nk$ for the full modular group $\mathrm{SL}_2(\mathbb{Z})$ inside $\mathrm{GL}_2(\mathbb{R})$ (written `𝒮ℒ`), all $P \in \mathbb{Z}[[q]]$ with `IsIntegralQExp F P`, and all $x \in \bar F$ whose underlying Laurent series equals $\bar P/\bar p_f^{\,n}$, one has $\Theta(x) =$ `qExpand K M` $(\bar P)/y^n$.
--
--   This is the characteristic-$\ell$ expansion at the cusp $0 = S\cdot\infty$ of the $q$-expansion model of the function field of $X_H(M)$: $\Theta$ is the reduction of the map sending a function to its expansion in the parameter $q_M$ after applying $S = \begin{pmatrix}0&-1\\1&0\end{pmatrix}$, the interchange of $\bar\jmath(q)$ and $\bar\jmath(q^M)$ recording the action of $S$ on the two $j$-values and the third clause recording that level-one forms are $S$-invariant and so expand at $0$ as at $\infty$ but in $q^M$, over a single non-zero series $y$ attached to $f$. It is used for the corresponding statement about the function field of $X_1$ built from the Igusa-type generators, [`ModularCurve.exists_algHom_igusaFunctionFieldX1C_apply_eq_jqNModC_and_apply_eq_jqModC`](thm.html#ModularCurve.exists_algHom_igusaFunctionFieldX1C_apply_eq_jqNModC_and_apply_eq_jqModC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ] :
    ∃ Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] LaurentSeries K,
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqModC K → Θ x = ModularCurve.jqNModC K M) ∧
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqNModC K M → Θ x = ModularCurve.jqModC K) ∧
      ∀ (k : ℤ) (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf : PowerSeries ℤ), ModularCurve.IsIntegralQExp f pf → ModularCurve.intSeriesC K pf ≠ 0 →
        ∃ y : LaurentSeries K, y ≠ 0 ∧
          ∀ (n : ℕ) (F : ModularForm 𝒮ℒ ((n : ℤ) * k)) (P : PowerSeries ℤ),
            ModularCurve.IsIntegralQExp F P →
            ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
              (x : LaurentSeries K) =
                ModularCurve.intSeriesC K P / ModularCurve.intSeriesC K pf ^ n →
              Θ x = ModularCurve.qExpand K M (ModularCurve.intSeriesC K P) / y ^ n := by sorry
