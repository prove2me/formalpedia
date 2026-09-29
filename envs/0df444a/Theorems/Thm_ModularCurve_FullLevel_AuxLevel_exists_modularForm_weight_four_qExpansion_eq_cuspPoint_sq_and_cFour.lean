-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour
-- name    : ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/d47e56bb-be54-5654-aee1-218f0221487c
-- title:
--   Weight-four forms with Tate cusp and c₄ q-expansions
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a non-zero natural number with $q\nmid M'$, let $\ell$ be a prime with $\ell\ge 3$, $\ell\neq q$ and $\ell\nmid M'$, let $L$ be a field of characteristic zero, let $\xi\in L$ be a primitive $q\ell$-th root of unity with associated unit $\xi_u\in L^\times$, and let $\iota:L\to\mathbb{C}$ be a ring homomorphism with $\iota(\xi)=\exp(2\pi i/(q\ell))$. Put $N=q\ell$ and let $\Gamma$ be the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those matrices in $\Gamma_0(N^2M')$ whose lower-right entry has unit class in the kernel of $(\mathbb{Z}/N^2M')^\times\to(\mathbb{Z}/N)^\times$, viewed inside $\mathrm{GL}_2(\mathbb{R})$. Then there are weight-$4$ modular forms $S_v$ for $\Gamma$, indexed by $v\in(\mathbb{Z}/N)^2$, and a weight-$4$ modular form $C_4$ for $\Gamma$, such that: (i) for every $v\neq 0$, the width-one $q$-expansion of $S_v$, read as a Laurent series over $\mathbb{C}$, is the image under coefficientwise application of $\iota$ of $\bigl((\mathrm{cuspPoint}\,L\,N\,\xi_u\,v)_1+1/12\bigr)^2$, the first (toric or non-toric, according as $v_1=0$ or not) coordinate of the explicit Tate cusp point shifted by $1/12$ and squared; (ii) the $q$-expansion of $C_4$ is likewise the image of $c_4$ of the Tate curve $\mathrm{tateBase}\,L\,N$ over $\mathrm{LaurentSeries}\,L$; and (iii) for every $\rho=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma_0(M')$, the weight-$4$ slash of $C_4$ by the matrix $\mathrm{conjElemN}\,N\,\rho=\begin{pmatrix}a&b/N\\Nc&d\end{pmatrix}$ equals $C_4$, while the same slash carries $S_v$ to $S_{(v_0 d+v_1 b,\;v_0 c+v_1 a)}$, the indices being reduced modulo $N$.
--
--   This supplies, at level $N^2M'$ with $N=q\ell$, weight-four holomorphic forms realising the $q$-expansions of the squared shifted $x$-coordinates at the cusps of the Tate curve and of its invariant $c_4$, together with the transformation law of the family under the $\Gamma_0(M')$-conjugated matrices $\mathrm{conjElemN}$. It is used by [`ModularCurve.FullLevel.AuxLevel.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq), where these forms are combined to produce forms matching the cusp-point coordinates themselves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    letI ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
    ∃ (Sw : (Fin 2 → ZMod (q * ℓ)) → ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 4)
      (C4 : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 4),
      (∀ v : Fin 2 → ZMod (q * ℓ), v ≠ 0 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Sw v))) =
          ModularCurve.coeffMap ι (((ModularCurve.cuspPoint L (q * ℓ) ξu v).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2)) ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C4)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L (q * ℓ)).c₄ ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C4 ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑C4 ∧
        ∀ v : Fin 2 → ZMod (q * ℓ),
          (⇑(Sw v) ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) =
            ⇑(Sw ![v 0 * ((ρ 1 1 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 1 : ℤ) : ZMod (q * ℓ)),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod (q * ℓ)) + v 1 * ((ρ 0 0 : ℤ) : ZMod (q * ℓ))])) := by sorry
