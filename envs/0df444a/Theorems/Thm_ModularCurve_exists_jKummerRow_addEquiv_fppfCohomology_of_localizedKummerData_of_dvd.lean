-- Prove2me | Theorems.Thm_ModularCurve_exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd
-- name    : ModularCurve.exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/8412bb6e-2627-51ef-81ca-d539462943a7
-- title:
--   Localised Kummer rows from integral Kummer data
-- statement:
--   Let $p$ and $q$ be primes, and assume $q$ divides $|p-1|/\gcd(p-1,12)$ (the numerator of $(p-1)/12$). Let $\mathcal J_m$, $m\in\mathbb N$, be sheaves of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb Z$, the site of $\mathbb Z$-schemes whose structure morphism is flat and locally of finite presentation, with the topology `smallFppfTopology`. Suppose given, for each $m$, abelian groups $M^0_m$, $H_m$, $(M^0_m)'$, $(H_m)'$ carrying module structures over $\mathbb T=$ `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]$, together with: a $\mathbb T$-linear map $\delta_m\colon M^0_m\to H_m$ whose kernel is the image of $q^m\cdot\mathrm{id}$ on $M^0_m$; the condition that $q^m$ annihilates $H_m$; $\mathbb T$-linear maps $\ell^0_m\colon M^0_m\to (M^0_m)'$ and $\ell^1_m\colon H_m\to (H_m)'$ realising $(M^0_m)'$, $(H_m)'$ as localisations at the complement of `eisensteinMaximalIdeal p q`, the preimage of $(q)\subseteq\mathbb Z$ under the character $\mathbb T\to\mathbb Z$ attached to the Eisenstein system at level $p$; an additive isomorphism $(H_m)'\cong H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z,\mathcal J_m)$; and, for a fixed abelian group $M$, injective homomorphisms $(M^0_m)'\to M$ with finite-index image. Then there is a family of data $\mathrm{row}_m\colon$ `JKummerRow q m M` — that is, groups $M_0$, $H^1_{\mathrm{tors}}$, $H^1$, an injection $M_0\to M$ of finite-index image, maps $\delta\colon M_0\to H^1_{\mathrm{tors}}$ and $\pi\colon H^1_{\mathrm{tors}}\to H^1$ with $\ker\delta=q^mM_0$, $\delta$ followed by $\pi$ exact, and $\operatorname{im}\pi=\ker(q^m\cdot\mathrm{id}_{H^1})$ — such that for every $m$ the group $\mathrm{row}_m.H1Jtors$ is additively isomorphic to $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z,\mathcal J_m)$.
--
--   This repackages the Kummer-sequence data of an abstract Néron identity component, after localisation at an Eisenstein maximal ideal of the Hecke algebra, into the abstract shape `JKummerRow` used downstream; it is the localised form of the Kummer sequence of the Néron model of $J_0(p)$ in Mazur's study of the Eisenstein ideal. It is cited in the construction of the Néron primary torsion core of $J_0(p)$ and in the corresponding nonemptiness statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem ModularCurve.exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (hqn : q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12)
    (𝒥 : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
    (M0int H1K M0loc H1Kloc : ℕ → Type)
    [∀ m, AddCommGroup (M0int m)] [∀ m, AddCommGroup (H1K m)]
    [∀ m, AddCommGroup (M0loc m)] [∀ m, AddCommGroup (H1Kloc m)]
    [∀ m, Module HeckeAlg (M0int m)] [∀ m, Module HeckeAlg (H1K m)]
    [∀ m, Module HeckeAlg (M0loc m)] [∀ m, Module HeckeAlg (H1Kloc m)]
    (δ : ∀ m, M0int m →ₗ[HeckeAlg] H1K m)
    (hδ : ∀ m, LinearMap.ker (δ m)
      = LinearMap.range ((q ^ m : HeckeAlg) • (LinearMap.id : M0int m →ₗ[HeckeAlg] M0int m)))
    (hH1K : ∀ m, ∀ x : H1K m, (q ^ m : HeckeAlg) • x = 0)
    (ℓ0 : ∀ m, M0int m →ₗ[HeckeAlg] M0loc m)
    [∀ m, IsLocalizedModule (eisensteinMaximalIdeal p q).primeCompl (ℓ0 m)]
    (ℓ1 : ∀ m, H1K m →ₗ[HeckeAlg] H1Kloc m)
    [∀ m, IsLocalizedModule (eisensteinMaximalIdeal p q).primeCompl (ℓ1 m)]
    (eH1 : ∀ m, H1Kloc m ≃+ fppfCohomology specInt (𝒥 m) 1)
    (M : Type) [AddCommGroup M] (toM : ∀ m, M0loc m →+ M)
    (htoM : ∀ m, Function.Injective (toM m)) (hfin : ∀ m, (toM m).range.FiniteIndex) :
    ∃ row : ∀ m, JKummerRow q m M,
      ∀ m, Nonempty (letI := (row m).instH1Jtors; (row m).H1Jtors ≃+ fppfCohomology specInt (𝒥 m) 1) := by sorry
