-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_six_qExpansion_eq_cSix_tateBase
-- name    : ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_six_qExpansion_eq_cSix_tateBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/4e90bbac-cb1d-5de1-b186-47f46cb010bd
-- title:
--   A weight-six form with q-expansion c₆ of the Tate curve
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $M'$ be a nonzero natural number not divisible by $q$, and let $\ell$ be a prime with $\ell \ge 3$, $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero, let $\xi \in L$ be a primitive $(q\ell)$-th root of unity, and let $\iota : L \to \mathbb{C}$ be a ring homomorphism with $\iota(\xi) = \exp(2\pi i/(q\ell))$. Put $N = q\ell$. The assertion is that there is a modular form $C_6$ of weight $6$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ coming from [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) of level $N^2M'$ and the subgroup [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22), i.e. the group of matrices in $\Gamma_0(N^2M')$ whose lower-right entry, viewed as a unit of $\mathbb{Z}/N^2M'$, lies in the kernel of reduction to $(\mathbb{Z}/N)^\times$, such that two things hold. First, the $q$-expansion of $C_6$ at width $1$, regarded as a Laurent series over $\mathbb{C}$, is the coefficientwise image under $\iota$ of the invariant $c_6$ of the Weierstrass curve [`ModularCurve.tateBase L N`](def/ModularCurve_TateSlots.html#L46), the formal Tate curve over $L$-Laurent series with the substitution $q \mapsto q^{N}$ applied. Secondly, for every $\rho \in \Gamma_0(M')$ the weight-$6$ slash of $C_6$ by the matrix $\begin{pmatrix} a & b/N \\ Nc & d\end{pmatrix}$ attached to $\rho = \begin{pmatrix} a & b \\ c& d\end{pmatrix}$ by [`ModularCurve.FullLevel.conjElemN`](def/ModularCurve_FullLevelLevelAutAt.html#L13) equals $C_6$.
--
--   Classically $c_6$ of the Tate curve over $\mathbb{Z}[[q]]$ is $-E_6$, so this realises $-E_6(q^{N})$, the weight-six Eisenstein series stretched by $\tau \mapsto N\tau$, as a modular form on the auxiliary full-level group that is moreover invariant under the twisted action of $\Gamma_0(M')$. It feeds the construction of modular forms whose ratio of $q$-expansions computes the cusp data of the Tate curve, used in the level-automorphism identification at level $q\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_six_qExpansion_eq_cSix_tateBase.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_six_qExpansion_eq_cSix_tateBase
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ C6 : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
            Subgroup (GL (Fin 2) ℝ)) 6,
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C6)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L (q * ℓ)).c₆ ∧
      ∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C6 ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) ρ) = ⇑C6 := by sorry
