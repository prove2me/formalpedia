-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_three_qExpansion_eq_cuspPoint
-- name    : ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_three_qExpansion_eq_cuspPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/e4f78d15-e17e-55ad-9b4b-c65b2c4ee173
-- title:
--   Weight-three forms with Tate cusp-point q-expansions
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a nonzero natural number not divisible by $q$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\neq q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell)$-th root of unity, and $\iota:L\to\mathbb{C}$ a ring homomorphism with $\iota(\xi)=\exp(2\pi i/(q\ell))$; write $\xi_u$ for $\xi$ viewed as a unit of $L$. The assertion is the existence of a family $R$ of modular forms of weight $3$, indexed by vectors $v\in(\mathbb{Z}/q\ell)^2$, for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ given by those $\gamma\in\Gamma_0((q\ell)^2M')$ whose lower-right entry reduces, in $(\mathbb{Z}/(q\ell)^2M')^\times$, into the kernel of reduction to $(\mathbb{Z}/q\ell)^\times$, subject to two conditions. First, for every $v\neq 0$ the Laurent series attached to the width-$1$ $q$-expansion of $R_v$ equals the coefficientwise image under $\iota$ of $2y_v+x_v$, where $(x_v,y_v)=\mathrm{cuspPoint}\,L\,(q\ell)\,\xi_u\,v$ is the Tate-curve cusp point: the toric series at $\xi_u^{\,(v_0)}$ when $v_1=0$, and otherwise the non-toric series at $\xi_u^{\,(v_0)}$ with index $(v_1)$, each taken with the representative values in $\{0,\dots,q\ell-1\}$. Second, for every $\rho=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ and every $v$, the weight-$3$ slash action on $R_v$ of the real matrix $\begin{pmatrix}a&b/(q\ell)\\ (q\ell)c&d\end{pmatrix}$ equals $R$ evaluated at the vector $(v_0 d+v_1 b,\;v_0 c+v_1 a)$ modulo $q\ell$.
--
--   This realises the $2y+x$ coordinates of the $(q\ell)$-torsion cusp points on the Tate curve as $q$-expansions of weight-three Eisenstein-type forms on the level $(q\ell)^2M'$ group cut out by the reduction condition modulo $q\ell$, together with the transformation law of the family under the twisted $\Gamma_0(M')$-action. It feeds the construction [`ModularCurve.FullLevel.AuxLevel.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_three_qExpansion_eq_cuspPoint.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_three_qExpansion_eq_cuspPoint
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    letI ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
    ∃ Rw : (Fin 2 → ZMod (q * ℓ)) → ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 3,
      (∀ v : Fin 2 → ZMod (q * ℓ), v ≠ 0 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rw v))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.cuspPoint L (q * ℓ) ξu v).2 + (ModularCurve.cuspPoint L (q * ℓ) ξu v).1)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' → ∀ v : Fin 2 → ZMod (q * ℓ),
        (⇑(Rw v) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) =
          ⇑(Rw ![v 0 * ((ρ 1 1 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 1 : ℤ) : ZMod (q * ℓ)),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 0 : ℤ) : ZMod (q * ℓ))])) := by sorry
