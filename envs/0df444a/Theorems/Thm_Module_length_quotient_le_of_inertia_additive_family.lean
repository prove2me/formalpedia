-- Prove2me | Theorems.Thm_Module_length_quotient_le_of_inertia_additive_family
-- name    : Module.length_quotient_le_of_inertia_additive_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/3bcbd6ec-e145-5e59-b8af-81b1058c7518
-- title:
--   Length bound for additive trace-zero families on inertia
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring (a domain), let $G$ be a group with a subgroup $I$, let $\sigma,\gamma \in G$ with $\gamma \in I$, and let $p,q,m$ be natural numbers such that the image of $p$ in $\mathcal{O}$ lies in the maximal ideal. Two hypotheses on $I$ are assumed: for every $\tau \in I$ there is $w \in I$ with $w^{p^m} = \sigma\tau\sigma^{-1}(\tau^{q})^{-1}$, and every $\tau \in I$ can be written as $\gamma^{j} x^{p^m} w^{p^m}$ for some $j \in \mathbb{N}$ and $x,w \in I$. Let $F,F' \in M_2(\mathcal{O})$ satisfy $FF' = 1$, $\operatorname{tr} F = a$ and $\det F = q$, with $q$ a unit in $\mathcal{O}$. Let $H$ be an $\mathcal{O}$-module and $\Lambda : H \to (G \to M_2(\mathcal{O}/\mathfrak{m}^m))$ an $\mathcal{O}$-linear map such that, for every $\varphi \in H$: $\Lambda\varphi$ is additive on $I$, i.e. $\Lambda\varphi(xy) = \Lambda\varphi(x) + \Lambda\varphi(y)$ for $x,y \in I$; $\Lambda\varphi(\sigma\tau\sigma^{-1}) = \bar F\,\Lambda\varphi(\tau)\,\bar F'$ for $\tau \in I$, where $\bar F,\bar F'$ are the entrywise reductions modulo $\mathfrak{m}^m$; and $\operatorname{tr}\Lambda\varphi(\tau) = 0$ for $\tau \in I$. Finally let $K \subseteq H$ be an $\mathcal{O}$-submodule containing every $\varphi$ with $\Lambda\varphi$ vanishing identically on $I$. Then the module length of $H/K$ is at most the length of $\mathcal{O}/\big((q-1)(a^2-(q+1)^2)\big)$.
--
--   This is the local computation at an auxiliary prime $q$ in the Taylor–Wiles style level-changing argument, in the form of a purely algebraic bound: an additive, trace-zero, $\sigma$-equivariant family of matrices on tame inertia is controlled by the cokernel of $F - q$ on trace-zero matrices, whose size divides $(q-1)(a^2-(q+1)^2)$. It is applied in [`GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnramifiedAt`](thm.html#GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnramifiedAt) to bound the length of a quotient measuring the change of level at an unramified prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_length_quotient_le_of_inertia_additive_family.lean

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.length_quotient_le_of_inertia_additive_family
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {G : Type} [Group G] (Isub : Subgroup G) (σ γ : G) (hγI : γ ∈ Isub) (p q m : ℕ)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ τ ∈ Isub, ∃ w ∈ Isub, w ^ (p ^ m) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (hgen : ∀ τ ∈ Isub, ∃ (j : ℕ) (x w : G), x ∈ Isub ∧ w ∈ Isub ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (F F' : Matrix (Fin 2) (Fin 2) 𝒪) (hFF' : F * F' = 1) (a : 𝒪) (htr : F.trace = a)
    (hdet : F.det = (q : 𝒪)) (hq : IsUnit (q : 𝒪))
    {H : Type} [AddCommGroup H] [Module 𝒪 H]
    (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m)))
    (hadd : ∀ φ : H, ∀ x ∈ Isub, ∀ y ∈ Isub, Λ φ (x * y) = Λ φ x + Λ φ y)
    (hequiv : ∀ φ : H, ∀ τ ∈ Isub, Λ φ (σ * τ * σ⁻¹) =
      F.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪) ^ m)) * Λ φ τ *
        F'.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪) ^ m)))
    (htr0 : ∀ φ : H, ∀ τ ∈ Isub, Matrix.trace (Λ φ τ) = 0)
    (K : Submodule 𝒪 H) (hK : ∀ φ : H, (∀ τ ∈ Isub, Λ φ τ = 0) → φ ∈ K) :
    Module.length 𝒪 (H ⧸ K) ≤
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {((q : 𝒪) - 1) * (a ^ 2 - ((q : 𝒪) + 1) ^ 2)}) := by sorry
