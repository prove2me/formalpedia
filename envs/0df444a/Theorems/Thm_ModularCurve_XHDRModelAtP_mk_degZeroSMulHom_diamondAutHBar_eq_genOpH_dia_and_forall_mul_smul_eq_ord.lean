-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord
-- name    : ModularCurve.XHDRModelAtP.mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/c59a34db-5b73-5cf4-8ee9-a0feff6b893f
-- title:
--   Diamond translate of a p-division datum on J_H(M)
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, a subgroup $H \le (\mathbb Z/M)^\times$, a set $S$ of naturals, and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤`; let $\mathfrak X$ be a model datum of type `XHDRModelAtP p M H hpM hj`, whose component `𝔛.Meta` is a curve model of the geometric function field $F =$ `xHFunctionFieldBar M H` over $K = \overline{\mathbb Q}$. Let `wgen` be a semilinear automorphism of $F$ over $K$ (a pair of ring automorphisms of $F$ and of $K$ compatible with the structure map), pinned by `hwgen` to the model automorphism $\mathfrak X.w$: whenever two $K$-points $y,y'$ of `𝔛.Meta.C` over the base satisfy that $y'$, followed by `𝔛.eeta`, the first pullback projection and $\mathfrak X.w$, equals $y$ followed by `𝔛.eeta` and that projection, then the place attached to $y'$ is `wgen` applied to the place attached to $y$. Let $e \in (\mathbb Z/M)^\times$, let $D$ be a degree-zero divisor on $F/K$ and $f \in F$ with $p\,(\mathrm{wgen}\cdot D)(v) = \operatorname{ord}_v f$ for every place $v$. Then: the class of $\sigma_e \cdot D$ in $J_H(M) = \mathrm{Pic}^0(K,F)$, where $\sigma_e =$ `diamondAutHBar M H e` is the chosen $K$-algebra automorphism of $F$ satisfying the $q$-expansion condition `IsDiamondAutHBar` for $e$ (the identity if none exists), equals `genOpH M H S (dia e)` applied to the class of $D$; and $p\,(\mathrm{wgen}\cdot(\sigma_e \cdot D))(v) = \operatorname{ord}_v(\sigma_e f)$ for every place $v$.
--
--   The statement says that the diamond operator $\langle e\rangle$ on $J_H(M)$ is, by construction, the map on degree-zero divisor classes induced by the diamond automorphism of the geometric function field, and that the pair $(D,f)$ witnessing $p\,(\mathrm{wgen}\cdot D) = \operatorname{div} f$ transports along $\langle e\rangle$ to the pair $(\sigma_e D, \sigma_e f)$. It is used in establishing the diamond-equivariance of the reduced root function attached to such a datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve ModularCurve.XHDRLevel
open ModularCurve in

theorem ModularCurve.XHDRModelAtP.mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)
    (e : (ZMod M)ˣ)
    (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (f : ↥(ModularCurve.xHFunctionFieldBar M H))
    (hDf : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) :
    (AlgebraicCurve.Pic0.mk (SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (diamondAutHBar M H e)) D) : ModularCurve.JH M H) =
        ModularCurve.genOpH M H S (CohCarrier.Gen.dia e) (AlgebraicCurve.Pic0.mk D) ∧
    ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • ((SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (diamondAutHBar M H e)) D :
          AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) :
            AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v =
        v.ord (diamondAutHBar M H e f) := by sorry
