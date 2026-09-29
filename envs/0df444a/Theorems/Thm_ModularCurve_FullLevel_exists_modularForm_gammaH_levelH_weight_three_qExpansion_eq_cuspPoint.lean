-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint
-- name    : ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/807c7aca-2356-58dd-922e-7128c193f151
-- title:
--   Weight-three forms realising the level-q Tate cusp points
-- statement:
--   Let $q$ be a prime, $M'$ a non-zero natural number with $q \nmid M'$, $L$ a field of characteristic zero, $\xi \in L$ a primitive $q$-th root of unity, and $\iota : L \to \mathbb{C}$ a ring homomorphism with $\iota(\xi) = e^{2\pi i/q}$; write $\xi_u$ for $\xi$ as a unit of $L$. Then there is a family $R_v$, indexed by $v \in (\mathbb{Z}/q)^2$, of modular forms of weight $3$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ determined by [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) at level $q^2M'$ and the subgroup $H =$ `levelH` $q\,M'$, the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ — that is, the image in $\mathrm{SL}_2(\mathbb{Z})$ of those $\gamma \in \Gamma_0(q^2M')$ whose lower-right entry, viewed as a unit mod $q^2M'$, lies in $H$ — such that: (i) for every $v \neq 0$, the $q$-expansion of $R_v$ with parameter $1$, read as a Laurent series, equals the coefficientwise image under $\iota$ of $2y_v + x_v$, where $(x_v, y_v) =$ `cuspPoint` $L\,q\,\xi_u\,v$ is the Tate toric point at $\xi^{v_0}$ when $v_1 = 0$ and otherwise the non-toric point with parameter $\xi^{v_0}$ and index $(v_1).\mathrm{val}$; and (ii) for every $\rho = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \Gamma_0(M')$ and every $v$, the weight-$3$ slash of $R_v$ by `conjElemN` $q\,\rho$, the matrix $\begin{pmatrix} a & b/q \\ qc & d \end{pmatrix} \in \mathrm{GL}_2(\mathbb{R})$, equals $R_w$ with $w = (v_0 d + v_1 b,\ v_0 c + v_1 a)$ in $(\mathbb{Z}/q)^2$.
--
--   This supplies the weight-three holomorphic forms, built from the level-$\Gamma(q)$ Eisenstein family, whose $q$-expansions are exactly the $\wp$-type coordinate combinations $2y_v + x_v$ of the Tate cusp points at level $q$, together with the index law for the $\Gamma_0(M')$-action through the conjugated matrices. It is the level-$q$ input to [`ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq`](thm.html#ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint.lean

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

theorem ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / q)) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    letI ξu : Lˣ := (hξ.isUnit (Fact.out : q.Prime).ne_zero).unit
    ∃ Rw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 3,
      (∀ v : Fin 2 → ZMod q, v ≠ 0 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rw v))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.cuspPoint L q ξu v).2 + (ModularCurve.cuspPoint L q ξu v).1)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' → ∀ v : Fin 2 → ZMod q,
        (⇑(Rw v) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) =
          ⇑(Rw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)])) := by sorry
