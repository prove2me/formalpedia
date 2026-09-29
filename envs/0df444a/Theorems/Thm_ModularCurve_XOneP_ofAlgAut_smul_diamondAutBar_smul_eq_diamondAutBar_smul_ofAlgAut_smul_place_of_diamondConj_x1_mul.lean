-- Prove2me | Theorems.Thm_ModularCurve_XOneP_ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul
-- name    : ModularCurve.XOneP.ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/06a4777a-8783-597f-b336-afdfd62fc469
-- title:
--   Conjugation of diamond operators on places of X₁(Mp)
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$, and let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $p$, equipped with an $L$-algebra structure on $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ with $K =$ `laurentBaseChange L (x1FunctionField (M * p))`, that is, the field generated over $L$ by the coefficientwise images of the $q$-expansion field of $\Gamma_1(Mp)$; write $\iota$ for the coefficientwise map $\mathrm{LaurentSeries}\,L \to \mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$ induced by $L \to \overline{\mathbb{Q}}$, and let $\overline{F} =$ `x1FunctionFieldBar (M * p)` be the corresponding field over $\overline{\mathbb{Q}}$. Given an $L$-algebra automorphism $\sigma$ of $K$ and a $\overline{\mathbb{Q}}$-algebra automorphism $\bar\sigma$ of $\overline{F}$ which is pinned to $\sigma$ coefficientwise (whenever $f \in \overline{F}$ has series $\iota(b)$ for some $b \in K$, the series of $\bar\sigma f$ is $\iota(\sigma b)$); natural numbers $d, d'$ coprime to $Mp$ with $d' \equiv d \pmod M$ and $d'd \equiv 1 \pmod p$; $L$-algebra automorphisms $\theta_d, \theta_{d'}$ of $K$ whose series agree with those of `baseChangeAut L (diamondAut (M * p) d)` and of the same for $d'$, and which are pinned coefficientwise, in the above sense, to `diamondAutBar (M * p) d` and `diamondAutBar (M * p) d'` respectively; and assuming $\sigma \theta_d \sigma^{-1} = \theta_{d'}$ as maps on series on $K$, the conclusion is that for every place $P$ of $\overline{F}$ over $\overline{\mathbb{Q}}$ (a valuation subring of $\overline{F}$ containing the image of $\overline{\mathbb{Q}}$, proper, and a principal ideal ring), one has $\mathrm{ofAlgAut}(\bar\sigma) \cdot (\mathrm{ofAlgAut}(\langle d\rangle) \cdot P) = \mathrm{ofAlgAut}(\langle d'\rangle) \cdot (\mathrm{ofAlgAut}(\bar\sigma) \cdot P)$, where $\langle d \rangle =$ `diamondAutBar (M * p) d` and `ofAlgAut` sends a $\overline{\mathbb{Q}}$-algebra automorphism to the semilinear automorphism $(\,\cdot\,, 1)$ acting on places.
--
--   This transports to places of the function field of $X_1(Mp)$ over $\overline{\mathbb{Q}}$ the relation $\bar\sigma \langle d \rangle \bar\sigma^{-1} = \langle d' \rangle$ between an automorphism coming from the level-$p$ part and the diamond operators, for $d' \equiv d \pmod M$ and $d'd \equiv 1 \pmod p$. It feeds the construction of reduction maps at places of $X_1(Mp)$ twisted by $\bar\sigma$, where a diamond has to be moved across the twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.XOneP.ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    [Algebra L (AlgebraicClosure ℚ)]

    (σ : ↥K ≃ₐ[L] ↥K)
    (σbar : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hσbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((σbar f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L))

    (d d' : ℕ) (hd : d.Coprime (M * p)) (hd' : d'.Coprime (M * p))
    (hdM : (d' : ZMod M) = (d : ZMod M)) (hdp : (d' : ZMod p) * (d : ZMod p) = 1)

    (θd θd' : ↥K ≃ₐ[L] ↥K)
    (hθd : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θd x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))
    (hθd' : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θd' x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))

    (hθdbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((ModularCurve.diamondAutBar (M * p) d f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((θd b : ↥K) : LaurentSeries L))
    (hθd'bar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((ModularCurve.diamondAutBar (M * p) d' f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((θd' b : ↥K) : LaurentSeries L))

    (hconj : ∀ x : ↥K, ((σ (θd (σ.symm x)) : ↥K) : LaurentSeries L) = ((θd' x : ↥K) : LaurentSeries L)) :
    ∀ P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)),
      AlgebraicCurve.SemilinearAut.ofAlgAut σbar • (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d) • P) =
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d') • (AlgebraicCurve.SemilinearAut.ofAlgAut σbar • P) := by sorry
