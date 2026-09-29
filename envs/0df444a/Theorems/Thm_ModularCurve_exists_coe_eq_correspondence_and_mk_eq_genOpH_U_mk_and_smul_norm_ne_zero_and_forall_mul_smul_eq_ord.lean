-- Prove2me | Theorems.Thm_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
-- name    : ModularCurve.exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/643e8e43-2677-5dc3-81f0-aa321eea94b2
-- title:
--   A root function for D pushes to one for Uₚ[D]
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$ and a set $S$ of natural numbers, and assume `HeckeDiamondInputsHAll M H`: the Hecke inputs `HeckeInputsHAlong` hold over $\overline{\mathbb{Q}}$ at every prime $\ell$, and every $d \in (\mathbb{Z}/M)^{\times}$ is realised by an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of $F :=$ `xHFunctionFieldBar M H` satisfying `IsDiamondAutHBar M H d σ`. Let `wgen` be a semilinear automorphism of $F$ over $\overline{\mathbb{Q}}$, that is, a pair consisting of a ring automorphism of $F$ and one of $\overline{\mathbb{Q}}$ compatible with the structure map, let $D$ be a divisor of degree zero on $F$, and let $f \ne 0$ in $F$ satisfy $p \cdot (\mathtt{wgen} \cdot D)(v) = \operatorname{ord}_v(f)$ at every place $v$ of $F/\overline{\mathbb{Q}}$. Then there exist: witnesses that `heckeAlphaHBar` and `heckeBetaHBar` at level $M p$ are integral ring maps, that the base-changed function field $\overline{\mathbb{Q}} \cdot F(\Gamma_H(M) \cap \Gamma_0(Mp))$ has principal divisors, that $\alpha :=$ `heckeAlphaHBar` is finite, together with the pushforward norm formula along $\alpha$; and a degree-zero divisor $D_U$ on $F$ such that $D_U$ equals the correspondence $\alpha_{*}\beta^{*}D$ with $\beta :=$ `heckeBetaHBar`, such that the class of $D_U$ in `JH M H` is `genOpH M H S` applied to the generator $U_p$ and to the class of $D$, such that $N := \mathtt{wgen} \cdot \mathrm{N}_{F'/F}\bigl(\beta(\mathtt{wgen}^{-1} \cdot f)\bigr)$ (norm taken for the $F$-algebra structure on $F'$ given by $\alpha$) is nonzero, and such that $p \cdot (\mathtt{wgen} \cdot D_U)(v) = \operatorname{ord}_v(N)$ for every place $v$.
--
--   This is the transport of a $p$-th root function along the $U_p$-correspondence on the Jacobian $J_H(M)$: a function whose divisor is $p$ times a translate of $D$ produces, by norm along the degeneracy map $\alpha$, a function whose divisor is $p$ times the corresponding translate of $\alpha_{*}\beta^{*}D$, whose class is $U_p[D]$. It is used in the analysis of reduced root functions attached to the $U_p$-operator at places of the modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : HeckeDiamondInputsHAll M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdivf : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v = v.ord f) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H p) (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H p)
      (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))))
      (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H p))
      (_ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H p) hfin)
      (D_U : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (D_U : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.correspondence (heckeBetaHBar (AlgebraicClosure ℚ) M H p) (heckeAlphaHBar (AlgebraicClosure ℚ) M H p) hβ hα
            (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
      (Pic0.mk D_U : JH M H) = genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) (Pic0.mk D) ∧
      (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
       wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H)) ≠ 0) ∧
      ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (p : ℤ) * (wgen • (D_U : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v =
          v.ord (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
                 wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H))) := by sorry
