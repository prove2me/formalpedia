-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar
-- name    : ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutHBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/c7235e78-9ad5-5686-8668-9c4005aefb0f
-- title:
--   Diamond automorphism lifts to the Hecke roof over Γ_H(M)
-- statement:
--   Let $M\ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/M\mathbb{Z})^\times$, let $\ell\ge 1$ and let $d\in(\mathbb{Z}/M\mathbb{Z})^\times$. Write $F$ for `laurentBaseChange (AlgebraicClosure ℚ)` applied to the $q$-expansion function field `xHFunctionField M H` of level $\Gamma_H(M)$, that is, the subfield of $\overline{\mathbb{Q}}(\!(q)\!)$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of that field of rational Laurent series, and write $F'$ for the corresponding base change of `xHTopFunctionFieldC ℚ M H (M * ℓ)`, the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the integral-form ratios attached to $\Gamma_H(M)\cap\Gamma_0(M\ell)$. Let $\alpha=$ `heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ` $: F\to F'$ be the degeneracy inclusion and $\beta=$ `heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ` the second degeneracy map, equal to `heckeBetaHBarOf` when the predicate `HeckeBetaHDefined M H ℓ` holds and to $\alpha$ otherwise; let $\sigma_d=$ `diamondAutHBar M H d` be the $\overline{\mathbb{Q}}$-algebra automorphism of $F$ chosen to satisfy `IsDiamondAutHBar M H d` when such an automorphism exists, and the identity otherwise. The assertion is that there exists a $\overline{\mathbb{Q}}$-algebra automorphism $\tau$ of $F'$ such that, viewing $\tau$ and $\sigma_d$ as semilinear automorphisms acting trivially on $\overline{\mathbb{Q}}$, one has $\tau(\alpha(x))=\alpha(\sigma_d x)$ and $\tau(\beta(x))=\beta(\sigma_d x)$ for every $x\in F$.
--
--   This is the function-field form of the classical fact that the diamond automorphism $\langle d\rangle$ of $X_H(M)$ lifts to the roof $X(\Gamma_H(M)\cap\Gamma_0(M\ell))$ of the $\ell$-th Hecke correspondence compatibly with both degeneracy maps, which is the geometric source of the commutation of diamond and Hecke operators. It is used by [`ModularCurve.heckeOperatorHAlong_diamondHBar_comm`](thm.html#ModularCurve.heckeOperatorHAlong_diamondHBar_comm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutHBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ τ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))
        ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutHBar M H d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutHBar M H d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) := by sorry
