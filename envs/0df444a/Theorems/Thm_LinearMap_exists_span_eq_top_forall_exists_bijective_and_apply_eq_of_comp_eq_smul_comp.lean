-- Prove2me | Theorems.Thm_LinearMap_exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp
-- name    : LinearMap.exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/7401ef9a-5143-5351-a462-a4615469950f
-- title:
--   Stone–von Neumann–Mackey over a ring, Zariski-locally
-- statement:
--   Let $R$ be a commutative ring and let $H$, $H'$ be finite abelian groups with $|H'| = |H|$ and with the image of $|H|$ in $R$ a unit. Let $e : H \times H' \to R^\times$ be a pairing that is additive-to-multiplicative in each variable separately, and that separates in the strong sense that for every $h \neq 0$ there is a $\chi$ with $e(h,\chi) - 1 \in R^\times$, and for every $\chi \neq 0$ there is an $h$ with $e(h,\chi) - 1 \in R^\times$. Let $M$ be an $R$-module equipped with a basis indexed by a finite type $\iota$ with $|\iota| = |H|$, and let $U : H \to \operatorname{End}_R(M)$ and $V : H' \to \operatorname{End}_R(M)$ satisfy $U_0 = \mathrm{id}$, $U_{h_1 + h_2} = U_{h_1} \circ U_{h_2}$, $V_0 = \mathrm{id}$, $V_{\chi_1 + \chi_2} = V_{\chi_1} \circ V_{\chi_2}$ and the Heisenberg relation $V_\chi \circ U_h = e(h,\chi)\,(U_h \circ V_\chi)$ for all $h$, $\chi$. The conclusion asserts the existence of an $n \in \mathbb{N}$ and elements $r_1, \dots, r_n \in R$ (indexed by `Fin n`) generating the unit ideal, such that for each index $j$: for every commutative $R$-algebra $R_j$ that is a localisation of $R$ away from $r_j$, every $R_j$-module $M_j$ which is also an $R$-module compatibly, every $R$-linear $\ell : M \to M_j$ realising $M_j$ as the localisation of $M$ at the powers of $r_j$, and every families of $R_j$-linear endomorphisms $U'_h$ and $V'_\chi$ of $M_j$ with $U'_h(\ell m) = \ell(U_h m)$ and $V'_\chi(\ell m) = \ell(V_\chi m)$ for all $m \in M$, there is a family $\sigma : H \to M_j$ such that the map $(c_h)_{h \in H} \mapsto \sum_h c_h \sigma_h$ from $H \to R_j$ to $M_j$ is bijective (so $\sigma$ is an $R_j$-basis of $M_j$ indexed by $H$), and $U'_k \sigma_h = \sigma_{k+h}$ and $V'_\chi \sigma_h = e(h,\chi)\,\sigma_h$ (the unit $e(h,\chi)$ acting through $R \to R_j$) for all $k, h \in H$, $\chi \in H'$.
--
--   This is the ring-theoretic form of the Stone–von Neumann–Mackey theorem used by Mumford in the theory of theta groups: a finite Heisenberg system on a free module of rank $|H|$, with $|H|$ invertible, acquires a Schrödinger basis after a Zariski-local refinement of the base. It is applied in [`AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts_of_isSectionBasis`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_cover_schrodingerFrame_of_levelLifts_of_isSectionBasis) to produce, over an open cover of the base, Schrödinger frames for the space of sections attached to a polarised abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_span_eq_top_forall_exists_bijective_and_apply_eq_of_comp_eq_smul_comp
    {R : Type u} [CommRing R]
    {H : Type v} [AddCommGroup H] [Fintype H]
    {H' : Type w} [AddCommGroup H'] [Fintype H']
    (hcard : Fintype.card H' = Fintype.card H) (hd : IsUnit ((Fintype.card H : ℕ) : R))
    (e : H → H' → Rˣ)
    (he₁ : ∀ (h₁ h₂ : H) (χ : H'), e (h₁ + h₂) χ = e h₁ χ * e h₂ χ)
    (he₂ : ∀ (h : H) (χ₁ χ₂ : H'), e h (χ₁ + χ₂) = e h χ₁ * e h χ₂)
    (hsep : ∀ h : H, h ≠ 0 → ∃ χ : H', IsUnit ((e h χ : R) - 1))
    (hsep' : ∀ χ : H', χ ≠ 0 → ∃ h : H, IsUnit ((e h χ : R) - 1))
    {M : Type u} [AddCommGroup M] [Module R M]
    {ι : Type u} [Fintype ι] (b : Module.Basis ι R M) (hrank : Fintype.card ι = Fintype.card H)
    (U : H → M →ₗ[R] M) (hU0 : U 0 = LinearMap.id) (hU : ∀ h₁ h₂ : H, U (h₁ + h₂) = U h₁ ∘ₗ U h₂)
    (V : H' → M →ₗ[R] M) (hV0 : V 0 = LinearMap.id) (hV : ∀ χ₁ χ₂ : H', V (χ₁ + χ₂) = V χ₁ ∘ₗ V χ₂)
    (hHeis : ∀ (h : H) (χ : H'), V χ ∘ₗ U h = (e h χ : R) • (U h ∘ₗ V χ)) :
    ∃ (n : ℕ) (r : Fin n → R), Ideal.span (Set.range r) = ⊤ ∧
      ∀ (j : Fin n) (Rj : Type u) [CommRing Rj] [Algebra R Rj] [IsLocalization.Away (r j) Rj]
        (Mj : Type u) [AddCommGroup Mj] [Module R Mj] [Module Rj Mj] [IsScalarTower R Rj Mj]
        (ℓ : M →ₗ[R] Mj) [IsLocalizedModule (Submonoid.powers (r j)) ℓ]
        (U' : H → Mj →ₗ[Rj] Mj) (_hU' : ∀ (h : H) (m : M), U' h (ℓ m) = ℓ (U h m))
        (V' : H' → Mj →ₗ[Rj] Mj) (_hV' : ∀ (χ : H') (m : M), V' χ (ℓ m) = ℓ (V χ m)),
        ∃ σ : H → Mj,
          Function.Bijective (fun c : H → Rj => ∑ h, c h • σ h) ∧
          (∀ k h : H, U' k (σ h) = σ (k + h)) ∧
          (∀ (χ : H') (h : H), V' χ (σ h) = algebraMap R Rj (e h χ : R) • σ h) := by sorry
