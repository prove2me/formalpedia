-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/7e58fa69-698d-5ea0-8060-838580ed8919
-- title:
--   Semiconjugating level automorphisms by a coefficientwise field automorphism
-- statement:
--   Let $L$ be a field of characteristic $0$, let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$, let $\ell_g \mid M'$, and let $\xi \in L$ be a primitive $q$-th root of unity. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of `levelH q M'` — the kernel of the unit reduction map `ZMod.unitsMap` along the divisibility `dvd_sq_mul q M'` — with the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell_g)^\times$. Let $K$ be an intermediate field of $L \subseteq L(\!(X)\!)$ (Laurent series over $L$), let $\sigma$ be a ring automorphism of $L$ and $\tau$ a ring automorphism of $K$ acting on Laurent series coefficientwise by $\sigma$, i.e. the image in $L(\!(X)\!)$ of $\tau x$ is `coeffMap` of $\sigma$ applied to that of $x$, for all $x \in K$. Then there is a unit $d \in (\mathbb{Z}/q)^\times$, independent of what follows, such that for every $\gamma \in \Gamma_0(M')$ and every $L$-algebra automorphism $g$ of $K$ satisfying `IsLevelAutAt L q ξ q (q^2*M') H₁ γ K g` there exist $\gamma' \in \Gamma_0(M')$ and an $L$-algebra automorphism $g'$ of $K$ with: $\gamma' \in \Gamma(q)$ whenever $\gamma \in \Gamma(q)$; the reduction `redQ q γ'` of $\gamma'$ in $\mathrm{GL}_2(\mathbb{Z}/q)$ equals $\mathrm{diag}(1,d)\,(\mathrm{redQ}\,q\,\gamma)\,\mathrm{diag}(1,d)^{-1}$; $\tau(g'x) = g(\tau x)$ for all $x \in K$; and `IsLevelAutAt L q ξ q (q^2*M') H₁ γ' K g'`. Here `IsLevelAutAt L n ζ m N₀ H γ K σ₀` asserts that for all weights $k$, all modular forms $f, g_0$ of weight $k$ for the group [`CohCarrier.GammaH N₀ H`](def/CohCarrier_Level.html#L133) viewed in $\mathrm{GL}_2(\mathbb{R})$, all integral power series $p_f, p_{g_0}$ which are their integral $q$-expansions with $p_{g_0}$ having nonzero image in $\mathbb{Q}(\!(X)\!)$, every $x \in K$ whose Laurent expansion is the image under `coeffEmb` of $p_f/p_{g_0}$, and every ring homomorphism $\iota : L \to \mathbb{C}$ sending $\zeta$ to $e^{2\pi i/n}$, one has $\iota_*(\sigma_0 x) \cdot (g_0 \mid_k \mathrm{conjElemN}\,m\,\gamma)^\wedge = (f \mid_k \mathrm{conjElemN}\,m\,\gamma)^\wedge$ as Laurent series, where ${}^\wedge$ denotes the $q$-expansion at $1$ and $\mathrm{conjElemN}\,m\,\gamma = \begin{pmatrix} a & b/m \\ mc & d\end{pmatrix}$ for $\gamma = \begin{pmatrix} a&b\\c&d\end{pmatrix}$.
--
--   This is the Shimura-reciprocity compatibility step at level $(q, H_1)$: it says that the family of level automorphisms attached to $\Gamma_0(M')$-matrices is stable, up to conjugating the mod-$q$ reduction by a fixed diagonal matrix $\mathrm{diag}(1,d)$, under conjugation by an automorphism of $K$ acting coefficientwise on Laurent series. It is used in the analysis of the linear part of the two-chart integral model, where the off-diagonal entry is shown to lie in the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt_of_eq_levelH_inf_ker.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open ModularCurve.FullLevel
open CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt_of_eq_levelH_inf_ker
    (L : Type) [Field L] [CharZero L]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L)) :
    ∃ d : (ZMod q)ˣ,
      ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (g : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K g →
        ∃ (γ' : SL(2, ℤ)) (g' : ↥K ≃ₐ[L] ↥K),
          γ' ∈ CongruenceSubgroup.Gamma0 M' ∧
          (γ ∈ CongruenceSubgroup.Gamma q → γ' ∈ CongruenceSubgroup.Gamma q) ∧
          redQ q γ' = diagOneElem q d * redQ q γ * (diagOneElem q d)⁻¹ ∧
          (∀ x : ↥K, τ (g' x) = g (τ x)) ∧
          ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ' K g' := by sorry
