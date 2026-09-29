-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour
-- name    : ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/e0d68df5-43eb-512b-b927-ad441bf305b0
-- title:
--   Weight-four forms with Tate cusp-point and c₄ expansions at level q
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number with $q \nmid M'$, let $L$ be a field of characteristic zero, let $\xi \in L$ be a primitive $q$-th root of unity, viewed also as a unit $\xi_u$ of $L$, and let $\iota : L \to \mathbb{C}$ be a ring homomorphism with $\iota(\xi) = \exp(2\pi i/q)$. Write $\Gamma$ for the subgroup [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) $(q^2M')$ `(ModularCurve.FullLevel.levelH` $q\,M')$ of $\mathrm{SL}(2,\mathbb{Z})$, namely the matrices of $\Gamma_0(q^2M')$ whose lower-right entry, read as a unit of $\mathbb{Z}/q^2M'$, lies in the kernel of reduction to $(\mathbb{Z}/q)^\times$, regarded as a subgroup of $\mathrm{GL}(2,\mathbb{R})$. The assertion is the existence of a family of weight-$4$ modular forms $S_v$ for $\Gamma$, indexed by $v \in (\mathbb{Z}/q)^2$, together with one further weight-$4$ modular form $C_4$ for $\Gamma$, such that: (i) for every $v \neq 0$, the width-$1$ $q$-expansion of $S_v$, read as a Laurent series over $\mathbb{C}$, is the image under $\iota$ (coefficientwise) of $\bigl(x_v + \tfrac{1}{12}\bigr)^2$, where $x_v$ is the first coordinate of [`ModularCurve.cuspPoint`](def/ModularCurve_KatzLevelPCusps.html#L59) $L\,q\,\xi_u\,v$, i.e. of the toric Tate point attached to $\xi^{(v_0)}$ when $v_1 = 0$ and of the non-toric point attached to $\xi^{(v_0)}$ and $(v_1)$ otherwise; (ii) the width-$1$ $q$-expansion of $C_4$ is the image under $\iota$ of the invariant $c_4$ of the Tate base curve [`ModularCurve.tateBase`](def/ModularCurve_TateSlots.html#L46) $L\,q$ over the Laurent series field; and (iii) for every $\rho = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{SL}(2,\mathbb{Z})$ lying in $\Gamma_0(M')$, the weight-$4$ slash of $C_4$ by $\rho^\sharp := \begin{pmatrix} a & b/q \\ qc & d\end{pmatrix} \in \mathrm{GL}(2,\mathbb{R})$ (the matrix [`ModularCurve.FullLevel.conjElemN`](def/ModularCurve_FullLevelLevelAutAt.html#L13) $q\,\rho$) equals $C_4$, while the weight-$4$ slash of $S_v$ by $\rho^\sharp$ equals $S_w$ with $w = (v_0 d + v_1 b,\; v_0 c + v_1 a)$, the entries of $\rho$ being reduced modulo $q$.
--
--   These are the weight-four Eisenstein-type forms on $\Gamma_{H}(q^2M')$ whose $q$-expansions realise, in the Tate parameter, the squares of the shifted $x$-coordinates of the $q$-torsion points of the Tate curve together with the invariant $c_4$, and whose slash action by the matrices $\rho^\sharp$ permutes the family by the natural right action of $\Gamma_0(M')$ on $(\mathbb{Z}/q)^2$. It is the level-$q$ input to [`ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq`](thm.html#ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / q)) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    letI ξu : Lˣ := (hξ.isUnit (Fact.out : q.Prime).ne_zero).unit
    ∃ (Sw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (C4 : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 4),
      (∀ v : Fin 2 → ZMod q, v ≠ 0 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Sw v))) =
          ModularCurve.coeffMap ι (((ModularCurve.cuspPoint L q ξu v).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2)) ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C4)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L q).c₄ ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C4 ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑C4 ∧
        ∀ v : Fin 2 → ZMod q,
          (⇑(Sw v) ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) =
            ⇑(Sw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)])) := by sorry
