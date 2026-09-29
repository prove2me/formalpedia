-- Prove2me | Theorems.Thm_LinearMap_exists_forall_localizedModule_mk_eq_of_forall_exists_chart
-- name    : LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/9bf0cce7-8652-5be4-840e-8b8b364d5df9
-- title:
--   Gluing a linear map from locally representable stalk maps
-- statement:
--   Let $B$ be a commutative ring and let $T$, $T'$ be $B$-modules. Suppose given a family $\varphi$ which assigns to every point $x$ of $\operatorname{Spec} B$ a $B$-linear map $\varphi_x$ from the localisation of $T'$ at the prime complement of $x$ to the localisation of $T$ at the same multiplicative set (localisations taken as `LocalizedModule`). Assume the family is locally representable in the following sense: for every prime $x$ there are an element $f \in B$ with $f \notin x$ and a $B$-linear map $\Phi : T' \to$ `LocalizedModule (Submonoid.powers f) T` such that for every prime $y$ with $f \notin y$, every $a \in T'$, every $t \in T$ and every $n \in \mathbb{N}$, if $\Phi(a)$ equals the class of $t$ over $f^n$ in $T[1/f]$, then for every element $s$ of the prime complement of $y$ with $s = f^n$ one has $\varphi_y(a/1) = t/s$ in the localisation of $T$ at $y$. The conclusion is that there exists a $B$-linear map $\tau : T' \to T$ such that for every prime $x$ and every $a \in T'$ the image $\tau(a)/1$ in the localisation of $T$ at $x$ equals $\varphi_x(a/1)$. Only existence of $\tau$ is asserted, not uniqueness.
--
--   This is the sheaf property of the $\mathcal{H}om$ sheaf $\mathcal{H}om(\widetilde{T'}, \widetilde{T})$ on $\operatorname{Spec} B$, stated in stalkwise form: a compatible family of maps on stalks which is locally given by a map into a single basic localisation comes from a global $B$-linear map. It is used in the Čerednik–Drinfel'd part of the development, where [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isIsomorphic_of_N_eq`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isIsomorphic_of_N_eq) invokes it to produce a global morphism from locally defined data, and its proof rests on the quasi-compactness of $\operatorname{Spec} B$ together with the gluing statement [`IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top`](thm.html#IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_forall_localizedModule_mk_eq_of_forall_exists_chart.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart
    {B : Type u} [CommRing B] {T T' : Type u} [AddCommGroup T] [Module B T] [AddCommGroup T'] [Module B T']
    (φ : ∀ x : PrimeSpectrum B,
      LocalizedModule x.asIdeal.primeCompl T' →ₗ[B] LocalizedModule x.asIdeal.primeCompl T)
    (hφ : ∀ x : PrimeSpectrum B, ∃ (f : B) (_ : f ∉ x.asIdeal)
        (Φ : T' →ₗ[B] LocalizedModule (Submonoid.powers f) T),
        ∀ (y : PrimeSpectrum B), f ∉ y.asIdeal → ∀ (a : T') (t : T) (n : ℕ),
          Φ a = LocalizedModule.mk t ⟨f ^ n, Submonoid.mem_powers_iff _ _ |>.mpr ⟨n, rfl⟩⟩ →
            ∀ s : y.asIdeal.primeCompl, (s : B) = f ^ n →
              φ y (LocalizedModule.mk a 1) = LocalizedModule.mk t s) :
    ∃ τ : T' →ₗ[B] T, ∀ (x : PrimeSpectrum B) (a : T'),
      LocalizedModule.mk (τ a) 1 = φ x (LocalizedModule.mk a 1) := by sorry
