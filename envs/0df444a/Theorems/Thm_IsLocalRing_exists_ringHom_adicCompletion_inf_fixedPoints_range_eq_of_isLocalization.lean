-- Prove2me | Theorems.Thm_IsLocalRing_exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
-- name    : IsLocalRing.exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/fafa5870-df88-5f53-9d47-a88945d76ebd
-- title:
--   Completion of invariants equals stabiliser-invariants of the completion
-- statement:
--   Let $k \subseteq K$ be fields with $K$ a $k$-algebra, let $G$ be a subgroup of the $k$-algebra automorphisms of $K$ with $G$ finite, and let $B$ be a subring of $K$ stable under every $\sigma \in G$. Let $BG$ be a subring characterised by $f \in BG \iff f \in B$ and $\sigma f = f$ for all $\sigma \in G$; assume $BG$ is noetherian and that, with the algebra structure given by the inclusion $BG \le B$, $B$ is a finite $BG$-module. Let $\tilde O$ be a subring of $K$ which is a local ring, with $B \le \tilde O$, and such that $f \in \tilde O$ exactly when $f h = g$ for some $g, h \in B$ with $h$ a unit of $\tilde O$ (a localisation of $B$ inside $K$). Let $H$ be the subgroup characterised by $\sigma \in H \iff \sigma \in G$ and $f \in \tilde O \iff \sigma f \in \tilde O$ for all $f \in K$, and let $O_0$ be the subring characterised by $f \in O_0 \iff f \in \tilde O$ and $\sigma f = f$ for all $\sigma \in G$. The conclusion asserts the existence of: noetherianity of $\tilde O$, locality and noetherianity of $O_0$, the inclusion $O_0 \le \tilde O$, a map $\mathrm{act}$ assigning to each $\sigma \in H$ a ring endomorphism of the $\mathfrak m_{\tilde O}$-adic completion $\widehat{\tilde O}$, and a ring homomorphism $\kappa \colon \widehat{O_0} \to \widehat{\tilde O}$ of the corresponding completions, such that: an element of $O_0$ is a unit iff its image in $\tilde O$ is a unit; for $\sigma \in H$ and $f \in \tilde O$ one has $\sigma f \in \tilde O$ and $\mathrm{act}\,\sigma$ carries the canonical image of $f$ to that of $\sigma f$; each $\mathrm{act}\,\sigma$ preserves the kernel of every level-$n$ evaluation $\widehat{\tilde O} \to \tilde O/\mathfrak m^n$; $\mathrm{act}\,\sigma$ is the unique ring endomorphism with these last two properties; and $\kappa$ is injective, compatible with the inclusion $O_0 \le \tilde O$ on canonical images, and has image exactly the set of $x \in \widehat{\tilde O}$ fixed by $\mathrm{act}\,\sigma$ for all $\sigma \in H$.
--
--   This is the classical description of the complete local ring of a quotient by a finite group at the image of a point: it is the ring of invariants of the stabiliser (decomposition group) acting on the complete local ring upstairs, with no tameness hypothesis. It is stated here entirely in terms of subrings of a field $K$, so as to be applied to local rings of modular curves and their quotients in the descent steps of the full-level analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) (hG : Finite ↥G)

    (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (BG : Subring K) (hBGdef : ∀ f : K, f ∈ BG ↔ f ∈ B ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f)
    (hBGnoeth : IsNoetherianRing ↥BG)
    (hfin : ∀ (hle : BG ≤ B), letI := (Subring.inclusion hle).toAlgebra; Module.Finite ↥BG ↥B)

    (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
    (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)

    (H : Subgroup (K ≃ₐ[k] K)) (hH : ∀ σ : K ≃ₐ[k] K, σ ∈ H ↔ σ ∈ G ∧ ∀ f : K, f ∈ Õ ↔ σ f ∈ Õ)
    (O₀ : Subring K) (hO₀ : ∀ f : K, f ∈ O₀ ↔ f ∈ Õ ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) :
    ∃ (_ : IsNoetherianRing ↥Õ) (_ : IsLocalRing ↥O₀) (_ : IsNoetherianRing ↥O₀) (hle : O₀ ≤ Õ)
      (act : ↥H → (AdicCompletion (maximalIdeal ↥Õ) ↥Õ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ))
      (κ : AdicCompletion (maximalIdeal ↥O₀) ↥O₀ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ),

      (∀ f : ↥O₀, IsUnit f ↔ IsUnit (Subring.inclusion hle f)) ∧

      (∀ (σ : ↥H) (f : ↥Õ), ∃ hσf : (σ : K ≃ₐ[k] K) (f : K) ∈ Õ,
        act σ (algebraMap ↥Õ _ f) = algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩) ∧
      (∀ (σ : ↥H) (n : ℕ) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
        AdicCompletion.evalₐ (maximalIdeal ↥Õ) n x = 0 → AdicCompletion.evalₐ (maximalIdeal ↥Õ) n (act σ x) = 0) ∧
      (∀ (σ : ↥H) (F : AdicCompletion (maximalIdeal ↥Õ) ↥Õ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
        (∀ f : ↥Õ, ∃ hσf : (σ : K ≃ₐ[k] K) (f : K) ∈ Õ, F (algebraMap ↥Õ _ f) = algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩) →
        (∀ (n : ℕ) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
          AdicCompletion.evalₐ (maximalIdeal ↥Õ) n x = 0 → AdicCompletion.evalₐ (maximalIdeal ↥Õ) n (F x) = 0) → F = act σ) ∧

      Function.Injective κ ∧
      (∀ f : ↥O₀, κ (algebraMap ↥O₀ _ f) = algebraMap ↥Õ _ (Subring.inclusion hle f)) ∧
      (∀ x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ, x ∈ Set.range κ ↔ ∀ σ : ↥H, act σ x = x) := by sorry
