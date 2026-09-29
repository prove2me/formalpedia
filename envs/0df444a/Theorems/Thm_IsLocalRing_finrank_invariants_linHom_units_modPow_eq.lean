-- Prove2me | Theorems.Thm_IsLocalRing_finrank_invariants_linHom_units_modPow_eq
-- name    : IsLocalRing.finrank_invariants_linHom_units_modPow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/337e7601-fb51-59a2-acca-20ac4f7bada2
-- title:
--   Units of a local ring: dimHom_Δ(N,R^×/(R^×)^q)
-- statement:
--   Fix a prime $q$ and a finite group $\Delta$ whose order is not divisible by $q$, and let $R$ be a local commutative domain with $q \neq 0$ in $R$, equipped with an action $act$ of $\Delta$ by ring automorphisms. Assume natural numbers $e < m$ with $(q) = \mathfrak{m}^e$ for $\mathfrak{m}$ the maximal ideal, that each $\mathfrak{m}^n$ has finite index as an additive subgroup, and that raising to the $q$-th power carries the subgroup $U^{(m)} = \{u \in R^\times : u - 1 \in \mathfrak{m}^m\}$ onto $U^{(m+e)}$; assume further that $U^{(m)}$ has no nontrivial $q$-torsion and that both $U^{(m)}$ and $U^{(m+e)}$ have finite index in $R^\times$. Let $\Lambda \le R$ be a $\Delta$-stable additive subgroup of finite index, and let $P_\Lambda$ on $V_\Lambda$ be a finite-dimensional $\mathbb{F}_q$-representation of $\Delta$ together with a surjection $\pi_\Lambda : \Lambda \to V_\Lambda$ whose kernel is exactly $q\Lambda$ and which is $\Delta$-equivariant, and suppose $V_\Lambda$ admits a basis indexed by $\Delta \times \iota$ ($\iota$ finite) permuted by $\Delta$ through the first coordinate. Let $N$, $P$, $T$ be finite-dimensional $\mathbb{F}_q$-representations of $\Delta$, where $P$ presents $R^\times/(R^\times)^q$ (a $\Delta$-equivariant surjection $\pi$ from $R^\times$ written additively, with kernel the $q$-th powers) and $T$ presents the $q$-torsion of $R^\times$ (a $\Delta$-equivariant injection $\iota_T$ into $R^\times$ with image exactly $\{u : u^q = 1\}$). Then $\dim_{\mathbb{F}_q}(N.\mathrm{linHom}\,P)^{\Delta} = |\iota| \cdot \dim_{\mathbb{F}_q} V_N + \dim_{\mathbb{F}_q}(N.\mathrm{linHom}\,T)^{\Delta}$.
--
--   This is the dimension-count form of the $\mathbb{F}_q[\Delta]$-module structure of the units of a tamely ramified local field: $\mathrm{Hom}_\Delta(N, R^\times/(R^\times)^q)$ exceeds $\mathrm{Hom}_\Delta(N, \mu_q)$ by the contribution $|\iota|\dim N$ coming from the free part. It is obtained by a dévissage along the finite-index subgroup $U^{(m)}$ of $R^\times$, using the corresponding count for $U^{(m)}$ itself and the $\Delta$-stability of the principal unit filtration, and it is used in turn for the analogous count for the units of a field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_finrank_invariants_linHom_units_modPow_eq.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Module

theorem IsLocalRing.finrank_invariants_linHom_units_modPow_eq
    {q : ℕ} [Fact q.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ)
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] (hqR : (q : R) ≠ 0)
    (act : Δ →* (R ≃+* R))
    {e m : ℕ} (he : Ideal.span {(q : R)} = maximalIdeal R ^ e) (hem : e < m)
    (hfin : ∀ n : ℕ, (maximalIdeal R ^ n).toAddSubgroup.FiniteIndex)
    (hpow : (principalUnits R m).map (powMonoidHom q) = principalUnits R (m + e))
    (hnotors : ∀ u ∈ principalUnits R m, u ^ q = 1 → u = 1) (hidxm : (principalUnits R m).FiniteIndex)
    (hidxme : (principalUnits R (m + e)).FiniteIndex)
    (Λ : AddSubgroup R) [Λ.FiniteIndex] (hΛ : ∀ (d : Δ) (x : R), x ∈ Λ → act d x ∈ Λ)
    {VΛ : Type*} [AddCommGroup VΛ] [Module (ZMod q) VΛ] [FiniteDimensional (ZMod q) VΛ]
    (PΛ : Representation (ZMod q) Δ VΛ) (πΛ : Λ →+ VΛ) (hπΛ : Function.Surjective πΛ)
    (hkerΛ : ∀ x : Λ, πΛ x = 0 ↔ ∃ y : Λ, q • y = x)
    (hπΛΔ : ∀ (d : Δ) (x : Λ), πΛ ⟨act d x, hΛ d x x.2⟩ = PΛ d (πΛ x))
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) (ZMod q) VΛ)
    (hb : ∀ (d d' : Δ) (i : ι), PΛ d (b (d', i)) = b (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)

    {VP : Type*} [AddCommGroup VP] [Module (ZMod q) VP] [FiniteDimensional (ZMod q) VP]
    (P : Representation (ZMod q) Δ VP)
    (π : Additive Rˣ →+ VP) (hπ : Function.Surjective π)
    (hkerπ : ∀ u : Rˣ, π (Additive.ofMul u) = 0 ↔ ∃ v : Rˣ, v ^ q = u)
    (hπΔ : ∀ (d : Δ) (u : Rˣ), π (Additive.ofMul (Units.map ((act d : R ≃+* R) : R →* R) u)) = P d (π (Additive.ofMul u)))

    {VT : Type*} [AddCommGroup VT] [Module (ZMod q) VT] [FiniteDimensional (ZMod q) VT]
    (T : Representation (ZMod q) Δ VT)
    (ιT : VT →+ Additive Rˣ) (hιT : Function.Injective ιT)
    (hranιT : ∀ u : Rˣ, Additive.ofMul u ∈ Set.range ιT ↔ u ^ q = 1)
    (hιTΔ : ∀ (d : Δ) (w : VT), Additive.toMul (ιT (T d w)) = Units.map ((act d : R ≃+* R) : R →* R) (Additive.toMul (ιT w))) :
    finrank (ZMod q) (N.linHom P).invariants
      = Fintype.card ι * finrank (ZMod q) VN + finrank (ZMod q) (N.linHom T).invariants := by sorry
