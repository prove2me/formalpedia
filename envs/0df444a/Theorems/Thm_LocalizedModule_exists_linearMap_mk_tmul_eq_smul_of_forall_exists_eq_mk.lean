-- Prove2me | Theorems.Thm_LocalizedModule_exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk
-- name    : LocalizedModule.exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/370b2b9f-a979-5194-aff7-bd106a5922a5
-- title:
--   Stalkwise family of maps spreads to one map near a point
-- statement:
--   Let $\mathcal{O}\to B$ be a homomorphism of commutative rings, let $M$ be a finite free $\mathcal{O}$-module, and let $T$ be a finitely generated $B$-module. Fix a prime $x$ of $B$ and an element $r_0\in B$ with $r_0\notin x$. Suppose given, for every prime $y$ of $B$ with $r_0\notin y$, a $B_y$-linear map $u_y : B_y\otimes_{\mathcal{O}}M \to T_y$, where $B_y$ denotes the localisation of $B$ at $y$ and $T_y$ the localisation of $T$ at the complement of $y$. Assume: (i) for every $v\in M$ there are $f\in B$ with $f\notin x$ and $t\in T$ such that $u_y(1\otimes v)=t/f$ in $T_y$ for every prime $y$ with $r_0\notin y$ and $f\notin y$; (ii) $u_x$ is surjective. Then there exist $r\in B$ with $r\notin x$ and $r_0\mid r$, and a $B$-linear map $A : B\otimes_{\mathcal{O}}M\to T$, such that for every prime $y$ with $r_0\notin y$ and $r\notin y$ and every $v\in M$ the image of $A(1\otimes v)$ in $T_y$ equals $r\cdot u_y(1\otimes v)$, and such that for every $t\in T$ there are $w\in B\otimes_{\mathcal{O}}M$ and $n\in\mathbb{N}$ with $A(w)=r^n t$.
--
--   This is the elementary statement that a morphism from the quasi-coherent sheaf attached to $B\otimes_{\mathcal{O}}M$ ($M$ finite free) to the one attached to a finitely generated module $T$ on $\operatorname{Spec} B$, known through its stalks over the basic open set $D(r_0)$ and continuous in the above sense at $x$, is induced up to the scalar $r$ by a single module homomorphism on a basic open neighbourhood of $x$, together with the spreading of surjectivity from a stalk to a neighbourhood (the last clause says that $A$ becomes surjective after inverting $r$). It is used in the Čerednik–Drinfeld part of the development, in [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_compatible_linearMap_pair_mk_tmul_eq_smul`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_compatible_linearMap_pair_mk_tmul_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalizedModule_exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem LocalizedModule.exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk
    {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {M : Type} [AddCommGroup M] [Module 𝒪 M] [Module.Free 𝒪 M] [Module.Finite 𝒪 M]
    {T : Type} [AddCommGroup T] [Module B T] [Module.Finite B T]
    (x : PrimeSpectrum B) (r₀ : B) (hr₀ : r₀ ∉ x.asIdeal)
    (u : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal →
      (Localization.AtPrime y.asIdeal ⊗[𝒪] M →ₗ[Localization.AtPrime y.asIdeal]
        LocalizedModule y.asIdeal.primeCompl T))
    (hcont : ∀ v : M, ∃ (f : B) (t : T), f ∉ x.asIdeal ∧
      ∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal) (hf : f ∉ y.asIdeal),
        u y hy ((1 : Localization.AtPrime y.asIdeal) ⊗ₜ[𝒪] v) = LocalizedModule.mk t ⟨f, hf⟩)
    (hsurj : Function.Surjective (u x hr₀)) :
    ∃ r : B, r ∉ x.asIdeal ∧ r₀ ∣ r ∧ ∃ A : B ⊗[𝒪] M →ₗ[B] T,
      (∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal), r ∉ y.asIdeal → ∀ v : M,
        LocalizedModule.mk (A ((1 : B) ⊗ₜ[𝒪] v)) 1 =
          algebraMap B (Localization.AtPrime y.asIdeal) r •
            u y hy ((1 : Localization.AtPrime y.asIdeal) ⊗ₜ[𝒪] v)) ∧
      (∀ t : T, ∃ (w : B ⊗[𝒪] M) (n : ℕ), A w = r ^ n • t) := by sorry
