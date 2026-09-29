-- Prove2me | Theorems.Thm_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist
-- name    : ModularCurve.exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/7d9986a8-0fb6-5d9e-8dc9-abd94ef1cc66
-- title:
--   qᵖ-expansion of the Atkin–Lehner conjugate of a Uₚ-norm
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$; assume `HeckeDiamondInputsHAll M H`, i.e. `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ for $M$, $H$ and every prime $\ell$, together with, for each $d \in (\mathbb{Z}/M)^\times$, a $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of $F :=$ `xHFunctionFieldBar M H` satisfying `IsDiamondAutHBar M H d`. Let $F' :=$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, the level-$M/p$ field for the image of $H$. Let `wgen` be a semilinear automorphism of $F$ over $\overline{\mathbb{Q}}$ (a compatible pair of ring automorphisms of $F$ and of $\overline{\mathbb{Q}}$), and let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F$ such that whenever $f \in F$ has the same Laurent series as some $u \in F'$, the Laurent series of $\theta f$ is `qExpand` of that of $u$, i.e. $u(q^p)$; assume `wgen` is the semilinear automorphism `SemilinearAut.ofAlgAut θ` attached to $\theta$. Let $\zeta \in \overline{\mathbb{Q}}^\times$ be a primitive $p$-th root of unity, and let $d \in (\mathbb{Z}/M)^\times$ reduce to $p$ in $\mathbb{Z}/(M/p)$, with $\pm$ its reduction lying in the image of $H$. Then for every $f \in F$ there is $c_0 \neq 0$ in $\overline{\mathbb{Q}}$ with $$\operatorname{qExpand}_p\Bigl(\mathrm{wgen} \cdot N\bigl(\beta(\mathrm{wgen}^{-1} \cdot f)\bigr)\Bigr) = c_0 \prod_{j=0}^{p-1} \operatorname{qTwist}(\zeta^j)(f)$$ in $\overline{\mathbb{Q}}((q))$, where $\beta =$ `heckeBetaHBar` maps $F$ into the level $\Gamma_H(M) \cap \Gamma_0(Mp)$ field, $N$ is the algebra norm for the $F$-algebra structure along the inclusion `heckeAlphaHBar`, and $\operatorname{qTwist}(u)$ multiplies the $k$-th Laurent coefficient by $u^k$.
--
--   This is the Atkin–Lehner $q$-expansion identity at a prime exactly dividing the level: the conjugate by the partial involution $w_p$ of the function realising $U_p$ (push-forward along the inclusion of the pull-back along the degeneracy map $q \mapsto q^p$) is, up to a constant, the product of the $p$ twists $q \mapsto \zeta^j q$ of the original function. It feeds the description of residues of differentials on $X_H(M)$ at $p$ in terms of Frobenius, used in the mod-$\ell$ model of the curve at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ p)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    (f : ↥(ModularCurve.xHFunctionFieldBar M H)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ c₀ : AlgebraicClosure ℚ, c₀ ≠ 0 ∧
      qExpand (AlgebraicClosure ℚ) p
          (((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
             wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H)
               (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) :
              ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        HahnSeries.C c₀ *
          ∏ j ∈ Finset.range p, ModularCurve.qTwist (ζ ^ j) ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by sorry
