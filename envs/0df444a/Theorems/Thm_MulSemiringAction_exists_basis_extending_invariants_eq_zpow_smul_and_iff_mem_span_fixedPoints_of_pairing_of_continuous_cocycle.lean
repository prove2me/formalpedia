-- Prove2me | Theorems.Thm_MulSemiringAction_exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle
-- name    : MulSemiringAction.exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/4f082380-cd1e-53dc-93e4-8734fde8e007
-- title:
--   Tate's splitting of a twisted semilinear pairing
-- statement:
--   Let $C$ be a topological field with a multiplicative action of a topological monoid $G$ by ring endomorphisms, let $\chi\colon G\to C^\times$ be a monoid homomorphism whose values are $G$-fixed and all of whose integral powers $\sigma\mapsto\chi(\sigma)^k$ are continuous, and assume: for every $k\neq0$ the only $c\in C$ with $\sigma\bullet c=\chi(\sigma)^k c$ for all $\sigma$ is $c=0$; and, for a fixed integer $m\neq0$, every continuous $c\colon G\to C$ with $c(\sigma\tau)=c(\sigma)+\chi(\sigma)^{-m}\,\sigma\bullet c(\tau)$ has the form $c(\sigma)=\chi(\sigma)^{-m}\sigma\bullet b-b$. Let $W$ be a finite-dimensional $C$-space with additive maps $\rho(\sigma)$ that are $\sigma$-semilinear, multiplicative in $\sigma$, and such that $\sigma\mapsto f(\rho(\sigma)w)$ is continuous for each $C$-linear functional $f$ and each $w$; let $W'$ be a $C$-space with $\sigma$-semilinear additive maps $\rho'(\sigma)$; let $B\colon W\to W'\to C$ be $C$-bilinear with $B(\rho(\sigma)w,\rho'(\sigma)w')=\chi(\sigma)^m\,\sigma\bullet B(w,w')$ and with $B(\,\cdot\,,w')=0$ forcing $w'=0$. Finally let $v\colon\iota\to W$ and $v'\colon\iota'\to W'$ be linearly independent families, over finite index types, of vectors fixed by all $\rho(\sigma)$, resp. all $\rho'(\sigma)$, with $|\iota|+|\iota'|=\dim_C W$. Then there is a $C$-basis $b$ of $W$ indexed by $\iota\sqcup\iota'$ with: $b(\mathrm{inl}\,i)=v_i$; $\rho(\sigma)b(\mathrm{inr}\,j)=\chi(\sigma)^m\cdot b(\mathrm{inr}\,j)$ for all $\sigma,j$; $B(b(\mathrm{inr}\,j),v'_{j'})=\delta_{jj'}$; the $\rho$-invariants of $W$ are exactly the span of the $v_i$ over the fixed subfield $C^G$; the $w$ with $\rho(\sigma)w=\chi(\sigma)^m w$ are exactly the $C^G$-span of the $b(\mathrm{inr}\,j)$; the $\rho'$-invariants of $W'$ are exactly the $C^G$-span of the $v'_j$; and for every $k\neq0,m$ the only $w$ with $\rho(\sigma)w=\chi(\sigma)^k w$ for all $\sigma$ is $w=0$.
--
--   This is the field-theoretic endgame of Tate's proof of the Hodge–Tate decomposition, isolated from its geometric inputs: under the two vanishing hypotheses (H0) and (H1) the semilinear representation $W$ splits as a sum of a weight-$0$ part and a weight-$m$ part, with no other weights, and the invariants are spanned over the fixed field by the given families. It is applied to the $C$-dual of the Tate module of a $p$-divisible group over a ring of integers, with $\chi$ the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MulSemiringAction_exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MulSemiringAction.exists_basis_extending_invariants_eq_zpow_smul_and_iff_mem_span_fixedPoints_of_pairing_of_continuous_cocycle
    {C : Type*} [Field C] [TopologicalSpace C] [IsTopologicalRing C]
    {G : Type*} [Monoid G] [TopologicalSpace G] [MulSemiringAction G C] (χ : G →* Cˣ)
    (hχ : ∀ k : ℤ, k ≠ 0 → ∀ c : C, (∀ σ : G, σ • c = (χ σ : C) ^ k * c) → c = 0)
    (hχG : ∀ σ τ : G, σ • (χ τ : C) = χ τ)
    (hχc : ∀ k : ℤ, Continuous fun σ : G => (χ σ : C) ^ k)
    (m : ℤ) (hm : m ≠ 0)
    (hH1 : ∀ c : G → C, Continuous c →
      (∀ σ τ : G, c (σ * τ) = c σ + (χ σ : C) ^ (-m) * σ • c τ) →
        ∃ b : C, ∀ σ : G, c σ = (χ σ : C) ^ (-m) * σ • b - b)
    {W : Type*} [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : G → W →+ W)
    (hρ : ∀ (σ : G) (c : C) (w : W), ρ σ (c • w) = (σ • c) • ρ σ w)
    (hρmul : ∀ (σ τ : G) (w : W), ρ (σ * τ) w = ρ σ (ρ τ w))
    (hρc : ∀ (f : W →ₗ[C] C) (w : W), Continuous fun σ : G => f (ρ σ w))
    {W' : Type*} [AddCommGroup W'] [Module C W'] (ρ' : G → W' →+ W')
    (hρ' : ∀ (σ : G) (c : C) (w' : W'), ρ' σ (c • w') = (σ • c) • ρ' σ w')
    (B : W →ₗ[C] W' →ₗ[C] C)
    (hB : ∀ (σ : G) (w : W) (w' : W'), B (ρ σ w) (ρ' σ w') = (χ σ : C) ^ m * σ • B w w')
    (hBr : ∀ w' : W', (∀ w : W, B w w' = 0) → w' = 0)
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (v : ι → W) (hv : ∀ (σ : G) (i : ι), ρ σ (v i) = v i) (hvi : LinearIndependent C v)
    (v' : ι' → W') (hv' : ∀ (σ : G) (j : ι'), ρ' σ (v' j) = v' j)
    (hvi' : LinearIndependent C v')
    (hcard : Fintype.card ι + Fintype.card ι' = Module.finrank C W) :
    ∃ b : Module.Basis (ι ⊕ ι') C W,
      (∀ i, b (Sum.inl i) = v i) ∧
      (∀ (σ : G) (j : ι'), ρ σ (b (Sum.inr j)) = ((χ σ : C) ^ m) • b (Sum.inr j)) ∧
      (∀ j, B (b (Sum.inr j)) (v' j) = 1 ∧ ∀ j', j' ≠ j → B (b (Sum.inr j)) (v' j') = 0) ∧
      (∀ w : W, (∀ σ : G, ρ σ w = w) ↔
        w ∈ Submodule.span (FixedPoints.subfield G C) (Set.range v)) ∧
      (∀ w : W, (∀ σ : G, ρ σ w = ((χ σ : C) ^ m) • w) ↔
        w ∈ Submodule.span (FixedPoints.subfield G C) (Set.range fun j => b (Sum.inr j))) ∧
      (∀ w' : W', (∀ σ : G, ρ' σ w' = w') ↔
        w' ∈ Submodule.span (FixedPoints.subfield G C) (Set.range v')) ∧
      (∀ (k : ℤ) (w : W), k ≠ 0 → k ≠ m → (∀ σ : G, ρ σ w = ((χ σ : C) ^ k) • w) → w = 0) := by sorry
