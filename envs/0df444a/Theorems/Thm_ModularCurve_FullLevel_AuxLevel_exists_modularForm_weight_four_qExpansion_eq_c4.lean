-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4
-- name    : ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_four_qExpansion_eq_c4
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/8736ac14-c154-5330-a88f-7aa9068ef8c1
-- title:
--   Weight-four form with q-expansion c₄ of the Tate curve
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $M'$ be a non-zero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \ge 3$, $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero, let $\xi \in L$ be a primitive $(q\ell)$-th root of unity, and let $\iota : L \to \mathbb{C}$ be a ring homomorphism with $\iota(\xi) = \exp(2\pi i/(q\ell))$. Write $\Gamma$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ determined by $\mathrm{GammaH}$ of level $(q\ell)^2M'$ and the group `levelH (q * ℓ) M'`, that is, the matrices of $\Gamma_0((q\ell)^2M')$ whose lower-right entry reduces to $1$ in $(\mathbb{Z}/(q\ell))^\times$ (the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/q\ell)^\times$). The assertion is that there exists a modular form $C_4$ of weight $4$ on $\Gamma$ such that, first, the period-$1$ $q$-expansion of $C_4$, regarded as a Laurent series over $\mathbb{C}$, is the coefficientwise image under $\iota$ of the invariant $c_4$ of the Weierstrass curve [`ModularCurve.tateBase L (q * ℓ)`](def/ModularCurve_TateSlots.html#L46) over $L((q))$ — the integral Tate curve pushed forward to Laurent series over $L$ and substituted $q \mapsto q^{q\ell}$ — and, second, for every $\rho \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ the weight-$4$ slash of $C_4$ by `conjElemN (q * ℓ) ρ`, the element of $\mathrm{GL}_2(\mathbb{R})$ with matrix $\begin{pmatrix} a & b/(q\ell) \\ (q\ell)c & d\end{pmatrix}$ for $\rho = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, equals $C_4$ as a function on the upper half-plane.
--
--   Classically the form produced here is $E_4((q\ell)\tau)$, whose expansion $1 + 240\sum_{n\ge 1}\sigma_3(n)\,q^{(q\ell)n}$ matches $c_4$ of the Tate curve $\mathrm{Tate}(q^{q\ell})$, and whose level-one origin accounts for the invariance under the conjugates $\mathrm{diag}(q\ell,1)^{-1}\rho\,\mathrm{diag}(q\ell,1)$ of $\Gamma_0(M')$. It is one of the weight-four ingredients used in [`ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour), where the squares of the $x$-coordinates of Tate torsion points are compared with $g_2 = c_4/12$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_four_qExpansion_eq_c4
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ C4 : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 4,
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C4)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L (q * ℓ)).c₄ ∧
      ∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C4 ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑C4 := by sorry
