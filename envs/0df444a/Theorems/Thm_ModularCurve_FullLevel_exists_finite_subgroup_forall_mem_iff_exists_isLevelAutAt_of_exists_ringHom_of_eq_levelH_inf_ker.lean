-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/fffffe7c-83b5-51fc-ad88-5d34e94547b0
-- title:
--   Finiteness of the Γ₀(M') level automorphisms at guarded level
-- statement:
--   Let $q$ be a prime and $M'\ge 1$ with $q\nmid M'$, let $\ell_g$ be a divisor of $M'$, and let $L$ be a field of characteristic $0$ containing a primitive $q$-th root of unity $\xi$ and admitting a ring homomorphism $\iota\colon L\to\mathbb C$ with $\iota(\xi)=e^{2\pi i/q}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb Z/q)^\times$ with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, and let $\Gamma_{H_1}(q^2M')\le\mathrm{SL}_2(\mathbb Z)$ be the image in $\mathrm{SL}_2(\mathbb Z)$ of the preimage of $H_1$ under $\Gamma_0(q^2M')\to(\mathbb Z/q^2M')^\times$. Let $K$ be the intermediate field of $L\subseteq L((X))$ generated over $L$ by the coefficientwise image under $\mathbb Q\to L$ of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ over $\mathbb Q$. The assertion is that there is a finite subgroup $G$ of $\mathrm{Aut}_L(K)$ whose elements are exactly those $\tau$ for which some $\gamma\in\Gamma_0(M')$ satisfies [`ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29), that is: for every weight $k\in\mathbb Z$, all modular forms $f,g$ of weight $k$ on $\Gamma_{H_1}(q^2M')$, all integral power series $p_f,p_g$ whose images in $\mathbb C[[X]]$ are the $q$-expansions (at width $1$) of $f$ and $g$, with the rational series attached to $p_g$ nonzero, every $x\in K$ whose underlying Laurent series is the image in $L((X))$ of the ratio of the rational series attached to $p_f$ and $p_g$, and every ring homomorphism $\iota\colon L\to\mathbb C$ sending $\xi$ to $e^{2\pi i/q}$, one has that the coefficientwise $\iota$-image of $\tau x$ times the $q$-expansion of $g\mid_k\delta$ equals the $q$-expansion of $f\mid_k\delta$, where $\delta=\operatorname{diag}(q,1)^{-1}\gamma^{-1}\operatorname{diag}(q,1)$.
--
--   This is the finiteness statement for the group of level automorphisms of the $q$-expansion function field at the guarded level $H_1$: the map sending $\gamma\in\Gamma_0(M')$ to the automorphism characterised by the displayed compatibility with $\operatorname{diag}(q,1)$-conjugated slash actions has image a finite subgroup of $\mathrm{Aut}_L(K)$, described exactly by the predicate [`ModularCurve.FullLevel.IsLevelAutAt`](def/ModularCurve_FullLevelLevelAutAt.html#L29). It supplies the finite-group input for the fixed-field (Artin) arguments used later in the study of the full-level $q$-expansion field and its integral models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :
    ∃ G : Subgroup (↥K ≃ₐ[L] ↥K), Finite G ∧
      ∀ τ : ↥K ≃ₐ[L] ↥K, τ ∈ G ↔ ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' ∧
        ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ⁻¹ K τ := by sorry
