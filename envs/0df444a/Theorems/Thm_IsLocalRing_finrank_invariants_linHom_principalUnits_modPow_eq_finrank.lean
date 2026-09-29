-- Prove2me | Theorems.Thm_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank
-- name    : IsLocalRing.finrank_invariants_linHom_principalUnits_modPow_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/ef9f7b2e-7d0d-54a8-8982-c63868a5c2c5
-- title:
--   Invariants of Hom(N,U^{(m)}/(U^{(m)})^q) under a coprime action
-- statement:
--   Let $q$ be a prime, $\Delta$ a finite group with $q \nmid |\Delta|$, and $R$ a commutative local domain in which $q \neq 0$, equipped with a homomorphism $\mathrm{act} : \Delta \to \operatorname{Aut}_{\mathrm{ring}}(R)$. Assume natural numbers $e < m$ with $(q) = \mathfrak{m}^{e}$ for $\mathfrak{m} = \mathrm{maximalIdeal}\,R$, that every $\mathfrak{m}^{n}$ has finite index as an additive subgroup of $R$, and that raising to the $q$th power carries the group $U^{(m)} = \{u \in R^{\times} : u - 1 \in \mathfrak{m}^{m}\}$ (the Lean `principalUnits R m`) onto $U^{(m+e)}$. Let $\Lambda \subseteq R$ be an additive subgroup of finite index with $\mathrm{act}\,d\,(\Lambda) \subseteq \Lambda$ for all $d$, and let $P_\Lambda$ be a representation of $\Delta$ on a finite-dimensional $\mathbb{Z}/q$-vector space $V_\Lambda$ together with a surjective additive map $\pi_\Lambda : \Lambda \to V_\Lambda$ whose kernel is exactly $q\Lambda$ and which is equivariant for $\mathrm{act}$ and $P_\Lambda$; assume $V_\Lambda$ has a basis indexed by $\Delta \times \iota$, with $\iota$ finite, on which $\Delta$ acts by left translation in the first coordinate: $P_\Lambda d\,(b(d',i)) = b(dd',i)$. Let $N$ be a representation of $\Delta$ on a finite-dimensional $\mathbb{Z}/q$-vector space $V_N$, and let $P_U$ be a representation of $\Delta$ on a $\mathbb{Z}/q$-vector space $V_U$ (no finiteness assumed) together with a surjective additive map $\pi_U$ from $U^{(m)}$, written additively, to $V_U$ whose kernel consists exactly of the $q$th powers in $U^{(m)}$ and which is equivariant in the sense that $\pi_U$ of the image of $u$ under $\mathrm{act}\,d$ equals $P_U d\,(\pi_U u)$ whenever that image lies in $U^{(m)}$. Then the space of $\Delta$-invariants of the representation $\operatorname{Hom}(V_N, V_U)$, i.e. of $\Delta$-equivariant $\mathbb{Z}/q$-linear maps $V_N \to V_U$, has dimension $|\iota| \cdot \dim_{\mathbb{Z}/q} V_N$.
--
--   This is the dimension count for $\operatorname{Hom}_{\Delta}\bigl(N, U^{(m)}/(U^{(m)})^{q}\bigr)$ attached to a group $\Delta$ of order prime to $q$ acting on a local ring whose deep principal units are, modulo $q$th powers, a free module over $\mathbb{F}_q[\Delta]$ up to finite-index and torsion corrections; the quotients $\Lambda/q\Lambda$ and $U^{(m)}/(U^{(m)})^{q}$ enter through surjections $\pi_\Lambda$, $\pi_U$ with prescribed kernels rather than as explicit quotient objects. It is used by [`IsLocalRing.finrank_invariants_linHom_units_modPow_eq`](thm.html#IsLocalRing.finrank_invariants_linHom_units_modPow_eq), where the full unit group replaces the deep principal units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_finrank_invariants_linHom_principalUnits_modPow_eq_finrank.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Module

theorem IsLocalRing.finrank_invariants_linHom_principalUnits_modPow_eq_finrank
    {q : ℕ} [Fact q.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ)
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] (hqR : (q : R) ≠ 0)
    (act : Δ →* (R ≃+* R))
    {e m : ℕ} (he : Ideal.span {(q : R)} = maximalIdeal R ^ e) (hem : e < m)
    (hfin : ∀ n : ℕ, (maximalIdeal R ^ n).toAddSubgroup.FiniteIndex)
    (hpow : (principalUnits R m).map (powMonoidHom q) = principalUnits R (m + e))
    (Λ : AddSubgroup R) [Λ.FiniteIndex] (hΛ : ∀ (d : Δ) (x : R), x ∈ Λ → act d x ∈ Λ)
    {VΛ : Type*} [AddCommGroup VΛ] [Module (ZMod q) VΛ] [FiniteDimensional (ZMod q) VΛ]
    (PΛ : Representation (ZMod q) Δ VΛ) (πΛ : Λ →+ VΛ) (hπΛ : Function.Surjective πΛ)
    (hkerΛ : ∀ x : Λ, πΛ x = 0 ↔ ∃ y : Λ, q • y = x)
    (hπΛΔ : ∀ (d : Δ) (x : Λ), πΛ ⟨act d x, hΛ d x x.2⟩ = PΛ d (πΛ x))
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) (ZMod q) VΛ)
    (hb : ∀ (d d' : Δ) (i : ι), PΛ d (b (d', i)) = b (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)
    {VU : Type*} [AddCommGroup VU] [Module (ZMod q) VU] (PU : Representation (ZMod q) Δ VU)
    (πU : Additive (principalUnits R m) →+ VU) (hπU : Function.Surjective πU)
    (hkerU : ∀ u : principalUnits R m,
      πU (Additive.ofMul u) = 0 ↔ ∃ v : principalUnits R m, v ^ q = u)
    (hπUΔ : ∀ (d : Δ) (u : principalUnits R m) (hu : Units.map ((act d : R ≃+* R) : R →* R) (u : Rˣ) ∈ principalUnits R m),
      πU (Additive.ofMul ⟨Units.map ((act d : R ≃+* R) : R →* R) u, hu⟩) = PU d (πU (Additive.ofMul u))) :
    finrank (ZMod q) (N.linHom PU).invariants = Fintype.card ι * finrank (ZMod q) VN := by sorry
