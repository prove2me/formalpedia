-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/b2e2c596-276f-52b7-b3ea-1b931c7db2b5
-- title:
--   Existence of level automorphisms at the guarded level H₁
-- statement:
--   Fix a prime $q$, a nonzero $M'$ with $q \nmid M'$, and a divisor $\ell_g$ of $M'$; let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$. Let $H_1 \le (\mathbb{Z}/q^2M')^{\times}$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction of units along $q \mid q^2M'$, with the kernel of the reduction of units along $\ell_g \mid q^2M'$. Let $K \subset L((q))$ be [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) applied to [`ModularCurve.xHFunctionField (q^2*M') H₁`](def/ModularCurve_XH.html#L79), i.e. the intermediate field generated over $L$ by the coefficientwise images of the field of $q$-expansions of modular functions for the subgroup [`CohCarrier.GammaH (q^2*M') H₁`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}(2,\mathbb{Z})$ (those elements of $\Gamma_0(q^2M')$ whose diagonal unit lies in $H_1$). Then for every $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ lying in $\Gamma_0(M')$ there is an $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q^2*M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29): for all $k \in \mathbb{Z}$, all weight-$k$ forms $f,g$ on [`CohCarrier.GammaH (q^2*M') H₁`](def/CohCarrier_Level.html#L133), all integral power series $p_f,p_g$ whose complex images are the $q$-expansions of $f,g$ with the Laurent series of $p_g$ over $\mathbb{Q}$ nonzero, all $x \in K$ whose Laurent series is the image in $L((q))$ of $\hat p_f/\hat p_g$, and all ring maps $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, one has $\iota(\tau x) \cdot \widehat{g\mid_k \gamma^{\sharp}} = \widehat{f\mid_k \gamma^{\sharp}}$, where $\gamma^{\sharp} = \mathrm{diag}(q,1)^{-1}\gamma^{-1}\,\mathrm{diag}(q,1)$ is `conjElemN q γ⁻¹`.
--
--   This is the existence half of Shimura's reciprocity description of the level automorphisms of the field of $q$-expansions attached to $\Gamma_{H_1}(q^2M')$, in the guarded form where the level subgroup is additionally cut down by the $\ell_g$-congruence condition. It supplies the Galois action on $K$ used throughout the full-level construction, in particular by the blow-up chart and Drinfeld-fibre arguments that invoke `IsLevelAutAt`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∃ τ : ↥K ≃ₐ[L] ↥K,
        ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ := by sorry
