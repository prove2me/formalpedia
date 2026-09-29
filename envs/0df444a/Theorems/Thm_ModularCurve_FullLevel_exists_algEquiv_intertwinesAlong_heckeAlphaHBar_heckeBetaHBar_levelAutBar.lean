-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar
-- name    : ModularCurve.FullLevel.exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/b416674f-7800-5bfa-aeb7-7c3075eb6f34
-- title:
--   Level automorphisms lift to the Hecke top curve
-- statement:
--   Let $q$ be prime, let $M'$ be a natural number with $q \nmid M'$, and let $\ell$ be a nonzero natural number with $q \nmid \ell$; put $N = q^2M'$ and let $H =$ `levelH q M'` be the kernel of the reduction $(\mathbb{Z}/N)^\times \to (\mathbb{Z}/q)^\times$. Assume `HeckeBetaHDefined`: for every $y$ in the function field `xHFunctionField N H`, the substituted Laurent series `qExpand ℚ ℓ y` lies in `xHTopFunctionFieldC ℚ N H (N * ℓ)`, the $q$-expansion function field of $\Gamma_H(N) \cap \Gamma_0(N\ell)$, where $\Gamma_H(N)$ is the preimage in $\Gamma_0(N)$ of $H$. Let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and let $x, x' \in \mathrm{SL}_2(\mathbb{Z})$ with $x' \in \Gamma_0(M')$ and, as integer matrices, $\mathrm{diag}(\ell,1)\,x = x'\,\mathrm{diag}(\ell,1)$. Then there is an $\overline{\mathbb{Q}}$-algebra automorphism $\tau$ of `laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H (N * ℓ))` — the subfield of $\overline{\mathbb{Q}}((X))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of that function field — such that, viewing automorphisms as semilinear automorphisms acting trivially on $\overline{\mathbb{Q}}$ via `ofAlgAut`, $\tau$ intertwines along both degeneracy maps: $\tau(\alpha(y)) = \alpha(\sigma_x(y))$ for all $y$, where $\alpha =$ `heckeAlphaHBar` is the inclusion of the base-changed field `laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField N H)` and $\sigma_x =$ `levelAutBar q M' ζ x`, and likewise $\tau(\beta(y)) = \beta(\sigma_{x'}(y))$ for $\beta =$ `heckeBetaHBar` (which, the hypothesis `HeckeBetaHDefined` being in force, is the branch `heckeBetaHBarOf` attached to the substitution `qExpand ℚ ℓ`) and $\sigma_{x'} =$ `levelAutBar q M' ζ x'`. Here `levelAutBar q M' ζ γ` denotes an automorphism of `fieldBar q M'` over $\overline{\mathbb{Q}}$ satisfying the predicate `IsLevelAutBar q M' ζ γ` when one exists, and the identity otherwise.
--
--   This is the compatibility of the two degeneracy maps of the Hecke correspondence of index $\ell$ on $X_H(q^2M')$ with the level automorphisms attached to matrices $\gamma^\sharp = \mathrm{diag}(q,1)^{-1}\gamma\,\mathrm{diag}(q,1)$, $\gamma \in \Gamma_0(M')$, on a fixed geometric component indexed by $\zeta$. It is used by [`ModularCurve.FullLevel.tateHecke_mul_tateGL2_comm`](thm.html#ModularCurve.FullLevel.tateHecke_mul_tateGL2_comm) to show that the Hecke operators commute with the $\mathrm{GL}_2(\mathbb{F}_q)$-action on the Jacobian of the full level $q$ modular curve over $\Gamma_0(M')$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel AlgebraicCurve

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') (ℓ : ℕ) [NeZero ℓ] (hqℓ : ¬ q ∣ ℓ)
    (hβ : ModularCurve.HeckeBetaHDefined (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ℓ)
    (ζ : ModularCurve.FullLevel.Idx q) (x x' : SL(2, ℤ)) (hx' : x' ∈ CongruenceSubgroup.Gamma0 M')
    (h : !![(ℓ : ℤ), 0; 0, 1] * (x : Matrix (Fin 2) (Fin 2) ℤ) =
      (x' : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1]) :
    ∃ τ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')
              (q ^ 2 * M' * ℓ))) ≃ₐ[AlgebraicClosure ℚ]
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')
              (q ^ 2 * M' * ℓ))),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (q ^ 2 * M')
            (ModularCurve.FullLevel.levelH q M') ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ x))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (q ^ 2 * M')
            (ModularCurve.FullLevel.levelH q M') ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ x'))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) := by sorry
