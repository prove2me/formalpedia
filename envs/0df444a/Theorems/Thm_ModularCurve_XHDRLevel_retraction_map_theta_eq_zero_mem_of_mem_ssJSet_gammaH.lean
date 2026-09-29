-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH
-- name    : ModularCurve.XHDRLevel.retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/186699c0-3e26-5b12-882c-664c784ebb95
-- title:
--   Supersingular points of the first copy lie on the second
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$; assume the Laurent series `jqModC ℚ` $= q^{-1}\cdot E_4^3\,\eta^{-24}$ lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ inside $\mathbb{Q}((q))$ by ratios of $q$-expansions of integrally normalised modular forms for $SL(2,\mathbb{Z})$. Write $\mathcal{O}_M$ and $\mathcal{O}_N$ for the $j$-finite chart algebras `chartAlgFin p (ΓM M H) hj` and `chartAlgFin p (ΓN p M H hpM) hj`, i.e. the elements of the respective $q$-expansion function fields integral over $(R\,p)[\,j\,]$, where $R\,p =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8). Given an $R\,p$-algebra map $\iota_0 : \mathcal{O}_N \to \mathcal{O}_M$ preserving $q$-expansions, an $R\,p$-algebra automorphism $\theta$ of $\mathcal{O}_M$ with $\theta(\iota_0 b)(q) = b(q^p)$ for all $b \in \mathcal{O}_N$ (i.e. `qExpand ℚ p` on $q$-expansions), an algebraically closed field $\kappa$ of characteristic $p$ that is an $R\,p$-algebra, and a $\kappa$-algebra map $\sigma_0 : \kappa \otimes_{R\,p} \mathcal{O}_M \to \kappa \otimes_{R\,p} \mathcal{O}_N$ retracting $\mathrm{id}_\kappa \otimes \iota_0$, the conclusion is: for every prime ideal $\mathfrak{p}$ of $\kappa \otimes_{R\,p} \mathcal{O}_N$ containing $1 \otimes j - a \otimes 1$ for some $a \in$ `ssJSet p κ` (those $a \in \kappa$ such that every elliptic curve over $\kappa$ with $j$-invariant $a$ has no nonzero $p$-torsion point), and every $x \in \kappa \otimes_{R\,p} \mathcal{O}_M$ with $\sigma_0((\mathrm{id}_\kappa \otimes \theta)(x)) = 0$, one has $\sigma_0(x) \in \mathfrak{p}$.
--
--   In the Deligne–Rapoport picture of the mod $p$ fibre of $X_H(M)$ for $p$ exactly dividing $M$, the fibre is the union of two copies of the level-$M/p$ curve crossing at the supersingular points; with $\sigma_1 = \sigma_0 \circ (\mathrm{id}_\kappa \otimes \theta)$ cutting out the second copy, this is the set-theoretic inclusion $\sigma_0(\ker \sigma_1) \subseteq \mathfrak{p}$ at a supersingular prime $\mathfrak{p}$ of the first copy. It feeds into [`ModularCurve.XHDRLevel.exists_retraction_tmul_theta_eq_zero_and_mem_iff_exists_mem_ssJSet`](thm.html#ModularCurve.XHDRLevel.exists_retraction_tmul_theta_eq_zero_and_mem_iff_exists_mem_ssJSet), where membership in the crossing locus is characterised by supersingularity of the $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.retraction_map_theta_eq_zero_mem_of_mem_ssJSet_gammaH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (σ₀ : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →ₐ[κ] κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
    (h0 : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) :
    ∀ 𝔭 : Ideal (κ ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)), 𝔭.IsPrime →
      (∃ a ∈ ssJSet p κ,
        (1 : κ) ⊗ₜ[R p] jChartFin p (ΓN p M H hpM) hj - a ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj)) ∈ 𝔭) →
      ∀ x : κ ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj),
        σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom x) = 0 → σ₀ x ∈ 𝔭 := by sorry
