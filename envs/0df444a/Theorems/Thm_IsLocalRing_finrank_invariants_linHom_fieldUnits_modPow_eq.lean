-- Prove2me | Theorems.Thm_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq
-- name    : IsLocalRing.finrank_invariants_linHom_fieldUnits_modPow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/d275abde-69a5-55dd-b1e5-b9fbb64aa0c0
-- title:
--   Dimension count for Hom_Δ(N,F^×/q)
-- statement:
--   Let $q$ be a prime, $\Delta$ a finite group with $q \nmid |\Delta|$, and $F$ a field in which $q \neq 0$, equipped with a homomorphism $\mathrm{actF} : \Delta \to \mathrm{Aut}(F)$ into the ring automorphisms of $F$. Let $Rs$ be a valuation subring of $F$ and $\mathrm{act} : \Delta \to \mathrm{Aut}(Rs)$ a homomorphism compatible with $\mathrm{actF}$ under the inclusion $Rs \subseteq F$. Assume: $q$ generates the $e$-th power of the maximal ideal of $Rs$ and $e < m$; every power of the maximal ideal has finite index as an additive subgroup; raising to the $q$-th power carries the subgroup $\{u \in Rs^\times : u - 1 \in \mathfrak{m}^m\}$ onto $\{u : u - 1 \in \mathfrak{m}^{m+e}\}$, the former having no $q$-torsion, and both having finite index in $Rs^\times$. Let $\Lambda \subseteq Rs$ be an additive subgroup of finite index stable under $\mathrm{act}$, let $V_\Lambda$ be a finite-dimensional $\mathbb{Z}/q$-vector space with a representation $P_\Lambda$ of $\Delta$, and let $\pi_\Lambda : \Lambda \to V_\Lambda$ be a surjective additive map, equivariant for $\mathrm{act}$ and $P_\Lambda$, whose kernel is exactly $q\Lambda$; assume $V_\Lambda$ has a basis indexed by $\Delta \times \iota$ ($\iota$ finite) permuted by $P_\Lambda$ via left translation in the first coordinate. Let $V_N$ be a finite-dimensional $\mathbb{Z}/q$-vector space with a representation $N$ of $\Delta$. Let $v : F^\times \to \mathrm{Multiplicative}\,\mathbb{Z}$ be a surjective homomorphism, invariant under the $\Delta$-action on $F^\times$, whose kernel consists of those $x$ with $x$ and $x^{-1}$ both in $Rs$. Finally, let $P_F$ be a representation of $\Delta$ on a $\mathbb{Z}/q$-vector space $V_{P_F}$ together with a surjective equivariant additive map $\pi_F : \mathrm{Additive}\,F^\times \to V_{P_F}$ whose kernel is the subgroup of $q$-th powers, and let $T_F$ be a representation on $V_{T_F}$ together with an injective equivariant additive map $\iota_F : V_{T_F} \to \mathrm{Additive}\,F^\times$ with image the $q$-torsion of $F^\times$. Then $$\dim_{\mathbb{Z}/q} (N.\mathrm{linHom}\,P_F)^{\Delta} = |\iota| \cdot \dim_{\mathbb{Z}/q} V_N + \dim_{\mathbb{Z}/q} (N.\mathrm{linHom}\,T_F)^{\Delta} + \dim_{\mathbb{Z}/q} (N.\mathrm{linHom}\,\mathbf{1})^{\Delta},$$ where $\mathbf{1}$ is the trivial representation of $\Delta$ on $\mathbb{Z}/q$.
--
--   This is the dimension count $\dim \mathrm{Hom}_\Delta(N, F^\times/(F^\times)^q) = |\iota|\dim N + \dim \mathrm{Hom}_\Delta(N,\mu_q) + \dim \mathrm{Hom}_\Delta(N,\mathbb{F}_q)$ for a field $F$ with a surjective $\Delta$-invariant valuation whose unit group is the given valuation subring, obtained from the corresponding count for $Rs^\times/(Rs^\times)^q$ together with additivity of $\Delta$-invariant homomorphism dimensions along the exact sequence with quotient $\mathbb{Z}/q$. It feeds the local computation of $\dim \mathrm{Hom}_\Delta(N, K_w^\times/(K_w^\times)^q)$ for a local field $K_w$ with a basis of the relevant lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Module

theorem IsLocalRing.finrank_invariants_linHom_fieldUnits_modPow_eq
    {q : ℕ} [Fact q.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ)
    {F : Type*} [Field F] (hqF : (q : F) ≠ 0) (actF : Δ →* (F ≃+* F))
    (Rs : ValuationSubring F) (act : Δ →* (Rs ≃+* Rs))
    (hact : ∀ (d : Δ) (x : Rs), ((act d x : Rs) : F) = actF d (x : F))
    {e m : ℕ} (he : Ideal.span {(q : Rs)} = maximalIdeal Rs ^ e) (hem : e < m)
    (hfin : ∀ n : ℕ, (maximalIdeal Rs ^ n).toAddSubgroup.FiniteIndex)
    (hpow : (principalUnits Rs m).map (powMonoidHom q) = principalUnits Rs (m + e))
    (hnotors : ∀ u ∈ principalUnits Rs m, u ^ q = 1 → u = 1) (hidxm : (principalUnits Rs m).FiniteIndex)
    (hidxme : (principalUnits Rs (m + e)).FiniteIndex)
    (Λ : AddSubgroup Rs) [Λ.FiniteIndex] (hΛ : ∀ (d : Δ) (x : Rs), x ∈ Λ → act d x ∈ Λ)
    {VΛ : Type*} [AddCommGroup VΛ] [Module (ZMod q) VΛ] [FiniteDimensional (ZMod q) VΛ]
    (PΛ : Representation (ZMod q) Δ VΛ) (πΛ : Λ →+ VΛ) (hπΛ : Function.Surjective πΛ)
    (hkerΛ : ∀ x : Λ, πΛ x = 0 ↔ ∃ y : Λ, q • y = x)
    (hπΛΔ : ∀ (d : Δ) (x : Λ), πΛ ⟨act d x, hΛ d x x.2⟩ = PΛ d (πΛ x))
    {ι : Type*} [Fintype ι] (b : Module.Basis (Δ × ι) (ZMod q) VΛ)
    (hb : ∀ (d d' : Δ) (i : ι), PΛ d (b (d', i)) = b (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)

    (v : Fˣ →* Multiplicative ℤ) (hv : Function.Surjective v)
    (hvker : ∀ x : Fˣ, v x = 1 ↔ ((x : F) ∈ Rs ∧ ((x⁻¹ : Fˣ) : F) ∈ Rs))
    (hvΔ : ∀ (d : Δ) (x : Fˣ), v (Units.map ((actF d : F ≃+* F) : F →* F) x) = v x)

    {VPF : Type*} [AddCommGroup VPF] [Module (ZMod q) VPF] (PF : Representation (ZMod q) Δ VPF)
    (πF : Additive Fˣ →+ VPF) (hπF : Function.Surjective πF)
    (hkerπF : ∀ u : Fˣ, πF (Additive.ofMul u) = 0 ↔ ∃ w : Fˣ, w ^ q = u)
    (hπFΔ : ∀ (d : Δ) (u : Fˣ), πF (Additive.ofMul (Units.map ((actF d : F ≃+* F) : F →* F) u)) = PF d (πF (Additive.ofMul u)))
    {VTF : Type*} [AddCommGroup VTF] [Module (ZMod q) VTF] (TF : Representation (ZMod q) Δ VTF)
    (ιF : VTF →+ Additive Fˣ) (hιF : Function.Injective ιF)
    (hranιF : ∀ u : Fˣ, Additive.ofMul u ∈ Set.range ιF ↔ u ^ q = 1)
    (hιFΔ : ∀ (d : Δ) (w : VTF), Additive.toMul (ιF (TF d w)) = Units.map ((actF d : F ≃+* F) : F →* F) (Additive.toMul (ιF w))) :
    finrank (ZMod q) (N.linHom PF).invariants
      = Fintype.card ι * finrank (ZMod q) VN + finrank (ZMod q) (N.linHom TF).invariants
        + finrank (ZMod q) (N.linHom (Representation.trivial (ZMod q) Δ (ZMod q))).invariants := by sorry
