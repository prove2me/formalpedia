-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt
-- name    : ModularCurve.FullLevel.exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/74df7b93-27fd-53e1-a9b5-a0b4f7b1a30d
-- title:
--   Finiteness of the group of level automorphisms attached to Γ₀(M')
-- statement:
--   Let $q\ge 5$ be a prime, let $M'$ be a non-zero natural number with $q\nmid M'$, let $L$ be a field of characteristic zero, and let $\zeta\in L$ be a primitive $q$-th root of unity such that there exists a ring homomorphism $\iota:L\to\mathbb{C}$ with $\iota\zeta=e^{2\pi i/q}$. Let $K$ be an intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ which equals [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) applied to the $q$-expansion function field $F(\Gamma_H(q^2M'))\subseteq\mathrm{LaurentSeries}\,\mathbb{Q}$, i.e. the subfield generated over $L$ by the coefficientwise image of that field under $\mathbb{Q}\to L$; here $H=$ [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$ and $\Gamma_H(q^2M')$ the corresponding subgroup of $\Gamma_0(q^2M')$. Let $\tau:\mathrm{SL}_2(\mathbb{Z})\to(K\simeq_{\mathrm{alg}[L]}K)$ be any function such that for every $\gamma\in\Gamma_0(M')$ the automorphism $\tau\gamma$ satisfies `IsLevelAutAt` for $\gamma^{-1}$: for all $k\in\mathbb{Z}$, all weight-$k$ forms $f,g$ on $\Gamma_H(q^2M')$ with integral $q$-expansions given by power series $p_f,p_g$ over $\mathbb{Z}$, with the series of $p_g$ over $\mathbb{Q}$ non-zero, and all $x\in K$ whose underlying Laurent series is the image in $L$ of the ratio of the rational $q$-expansions of $f$ and $g$, and every $\iota:L\to\mathbb{C}$ sending $\zeta$ to $e^{2\pi i/q}$, one has $\iota(x)\cdot(g\mid_k \gamma^{-\sharp})^{\wedge}=(f\mid_k \gamma^{-\sharp})^{\wedge}$ as $q$-expansions, where $\gamma^{-\sharp}$ is the conjugate of $\gamma^{-1}$ by $\mathrm{diag}(1,q)$ and ${}^{\wedge}$ denotes the $q$-expansion of width $1$. The conclusion is that there is a subgroup $G$ of the group of $L$-algebra automorphisms of $K$ which is finite and whose elements are exactly the $\tau\gamma$ for $\gamma\in\Gamma_0(M')$.
--
--   This records that the level automorphisms of $K=L\cdot F(\Gamma_H(q^2M'))$ attached to the elements of $\Gamma_0(M')$ constitute a single finite group of $L$-automorphisms of $K$, so that Galois-theoretic arguments (fixed fields, ramification and inertia) may be applied to them. It is used in the study of the extension $K$ over the $\Gamma_0$-level field, notably in the statements about comparison of ramification indices and separability, about the cyclic inertia action on the chart algebra, and about the supersingular $j$-locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))

    (τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K))
    (hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ))
    :
    ∃ G : Subgroup (↥K ≃ₐ[L] ↥K), Finite ↥G ∧
      ∀ σ : ↥K ≃ₐ[L] ↥K, σ ∈ G ↔ ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' ∧ σ = τ γ := by sorry
