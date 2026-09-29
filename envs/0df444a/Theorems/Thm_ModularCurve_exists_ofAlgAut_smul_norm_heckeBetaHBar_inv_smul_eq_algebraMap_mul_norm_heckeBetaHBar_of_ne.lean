-- Prove2me | Theorems.Thm_ModularCurve_exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne
-- name    : ModularCurve.exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/9528c832-e9cf-5662-a10e-a26b980ada91
-- title:
--   Atkin–Lehner pin commutes with the Hecke norm up to a scalar
-- statement:
--   Fix a prime $p$ and $M \ge 1$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), that is: `HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ` holds for every prime $\ell$, and for each $d \in (\mathbb{Z}/M)^\times$ there is an $\overline{\mathbb{Q}}$-automorphism $\sigma$ of $F :=$ `xHFunctionFieldBar M H` with `IsDiamondAutHBar M H d σ`; here $F$ is the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the rational $q$-expansion field `xHFunctionField M H`. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $F$ satisfying the $q$-expansion pin: whenever $f \in F$ and $u \in$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` have the same Laurent series, the series of $\theta f$ is `qExpand` $p$ of that of $u$, i.e. the substitution $q \mapsto q^p$ on exponents; the level group `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Let $\ell$ be a prime with $\ell \ne p$ and $f \in F$. Write $\alpha :=$ `heckeAlphaHBar` for the inclusion of $F$ into $F_{\mathrm{top}} :=$ `laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ))`, and $\beta :=$ `heckeBetaHBar` for the map $q \mapsto q^\ell$ from $F$ to $F_{\mathrm{top}}$ when `HeckeBetaHDefined M H ℓ` holds (every $y$ in `xHFunctionField M H` has `qExpand ℚ ℓ y` in `xHTopFunctionFieldC ℚ M H (M * ℓ)`) and for $\alpha$ otherwise. Then there exists $c \in \overline{\mathbb{Q}}$, $c \ne 0$, with $\theta\bigl(N_{\alpha}(\beta(\theta^{-1} f))\bigr) = c \cdot N_{\alpha}(\beta f)$, where $N_\alpha$ is `Algebra.norm` for the $F$-algebra structure on $F_{\mathrm{top}}$ induced by $\alpha$, and $\theta$ acts through `SemilinearAut.ofAlgAut`, which regards $\theta$ as the pair $(\theta, \mathrm{id}_{\overline{\mathbb{Q}}})$.
--
--   This is the function-field form of the classical fact that the partial Atkin–Lehner involution $w_p$ at the exactly dividing prime $p$ commutes with the Hecke correspondence at a prime $\ell \ne p$, here in its multiplicative shape $f \mapsto N_\alpha(\beta f)$ on the function field of $X_H(M)$ over $\overline{\mathbb{Q}}$, the commutation being asserted only up to a nonzero scalar. It feeds the identification of reduced root functions and the norm of the mod-$\ell$ Hecke beta map used in the study of the $\ell$-torsion of Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne.lean

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

theorem ModularCurve.exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (f : ↥(ModularCurve.xHFunctionFieldBar M H)) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      SemilinearAut.ofAlgAut θ • (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ);
          (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ ((SemilinearAut.ofAlgAut θ)⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) =
        algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) c * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ);
          (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) := by sorry
