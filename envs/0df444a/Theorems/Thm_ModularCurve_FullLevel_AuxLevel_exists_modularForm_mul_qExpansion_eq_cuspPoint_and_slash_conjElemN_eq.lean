-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
-- name    : ModularCurve.FullLevel.AuxLevel.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/945d862d-10a2-54c3-958d-64d183d80d4f
-- title:
--   Modular forms realising Tate cusp coordinates and c₄,c₆
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a nonzero natural number not divisible by $q$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell)$-th root of unity with associated unit $\xi_u\in L^\times$, and $\iota:L\to\mathbb{C}$ a ring homomorphism with $\iota(\xi)=\exp(2\pi i/(q\ell))$. Write $\Gamma$ for the group [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) of level $(q\ell)^2M'$ attached to [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22), i.e. the matrices of $\Gamma_0((q\ell)^2M')$ whose lower-right entry reduces into the kernel of $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$, viewed inside $\mathrm{GL}_2(\mathbb{R})$. Then there exist families $A_w,B_w,R_w$ of modular forms on $\Gamma$ of weights $6,4,3$, indexed by $v\in(\mathbb{Z}/q\ell)^2$, and forms $C_4,C_6$ on $\Gamma$ of weights $4,6$, such that: for every $v\ne 0$ the $q$-expansion (at width $1$, read as a Laurent series over $\mathbb{C}$) of $B_w(v)$ is nonzero and lies in the image of [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) $\iota$, the image under $\iota$ of the first coordinate of [`ModularCurve.cuspPoint`](def/ModularCurve_KatzLevelPCusps.html#L59) $L\,(q\ell)\,\xi_u\,v$ plus the constant $1/12$ times the expansion of $B_w(v)$ equals the expansion of $A_w(v)$, and the expansion of $R_w(v)$ is the image under $\iota$ of twice the second coordinate plus the first coordinate of that cusp point; the expansions of $C_4$ and $C_6$ are the images under $\iota$ of the invariants $c_4$ and $c_6$ of [`ModularCurve.tateBase`](def/ModularCurve_TateSlots.html#L46) $L\,(q\ell)$; and for every $\rho=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$, with $\rho^{\sharp}=$ [`ModularCurve.FullLevel.conjElemN`](def/ModularCurve_FullLevelLevelAutAt.html#L13) $(q\ell)\,\rho=\begin{pmatrix}a&b/(q\ell)\\(q\ell)c&d\end{pmatrix}$, the forms $C_4$ and $C_6$ are invariant under the weight $4$, resp. weight $6$, slash action of $\rho^{\sharp}$, while for every $v$ the slash of $A_w(v)$ in weight $6$, of $B_w(v)$ in weight $4$ and of $R_w(v)$ in weight $3$ by $\rho^{\sharp}$ equals the corresponding form at the index $(v_0 d+v_1 b,\;v_0 c+v_1 a)$ in $(\mathbb{Z}/q\ell)^2$.
--
--   This provides the analytic input for the Tate model at level $q\ell$: the coordinates of the cusp sections of the Tate curve, and its invariants $c_4$, $c_6$, are expressed as ratios of $q$-expansions of holomorphic modular forms of weight $\le 6$ on a $\Gamma_H$-type group, together with the transformation law of the family under the normalised conjugates $\rho^{\sharp}$ of elements of $\Gamma_0(M')$. It is used in the construction of the Tate curve model over the relevant function field and in the identification of the level automorphisms acting on the cusp data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    letI ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
    ∃ (Aw : (Fin 2 → ZMod (q * ℓ)) → ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 6)
      (Bw : (Fin 2 → ZMod (q * ℓ)) → ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (Rw : (Fin 2 → ZMod (q * ℓ)) → ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 3)
      (C4 : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (C6 : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 6),
      (∀ v : Fin 2 → ZMod (q * ℓ), v ≠ 0 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) ≠ 0 ∧
        (∃ b : LaurentSeries L, HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) = ModularCurve.coeffMap ι b) ∧
        ModularCurve.coeffMap ι ((ModularCurve.cuspPoint L (q * ℓ) ξu v).1 + HahnSeries.C ((12 : L)⁻¹)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Bw v))) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Aw v))) ∧
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rw v))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.cuspPoint L (q * ℓ) ξu v).2 + (ModularCurve.cuspPoint L (q * ℓ) ξu v).1)) ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C4)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L (q * ℓ)).c₄ ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C6)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L (q * ℓ)).c₆ ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C4 ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑C4 ∧
        (⇑C6 ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑C6 ∧
        ∀ v : Fin 2 → ZMod (q * ℓ),
          (⇑(Aw v) ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑(Aw ![v 0 * ((ρ 1 1 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 1 : ℤ) : ZMod (q * ℓ)),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 0 : ℤ) : ZMod (q * ℓ))]) ∧
          (⇑(Bw v) ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑(Bw ![v 0 * ((ρ 1 1 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 1 : ℤ) : ZMod (q * ℓ)),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 0 : ℤ) : ZMod (q * ℓ))]) ∧
          (⇑(Rw v) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑(Rw ![v 0 * ((ρ 1 1 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 1 : ℤ) : ZMod (q * ℓ)),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 0 : ℤ) : ZMod (q * ℓ))])) := by sorry
