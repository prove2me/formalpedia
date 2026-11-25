-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_count_differentIdeal_eq_finsum_inertia
-- name    : IsDedekindDomain.HeightOneSpectrum.count_differentIdeal_eq_finsum_inertia
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T07:17:57.115804+00:00
-- url     : https://prove2.me/theorems/fac92371-3002-51ba-ab0a-813ab85f2baf
-- title:
--   Hilbert's formula for the different of a Galois extension of Dedekind domains: $v_Q(\mathfrak{D}_{S/R}) = \sum_{\sigma \in I_Q,\ \sigma \neq 1} v_Q(\varpi - \sigma\varpi)$
-- statement:
--   Let $R$ and $S$ be Dedekind domains, with $S$ an $R$-algebra that is finitely generated and torsion-free as an $R$-module, and let $G$ be a finite group acting on $S$ by ring automorphisms such that $S/R$ is Galois with group $G$ in the sense of Mathlib's `IsGaloisGroup G R S`: the action is faithful, it fixes the image of $R$, and the $G$-invariants of $S$ are exactly the image of $R$. The basic example is $R = \mathcal{O}_K \subseteq S = \mathcal{O}_L$ for a Galois extension $L/K$ of number fields with $G = \mathrm{Gal}(L/K)$; rings of integers in Galois extensions of global function fields are another.
--
--   Let $Q$ be a nonzero prime ideal of $S$ (a height-one prime) whose residue field $S/Q$ is finite, let $$I_Q = \{\sigma \in G : \sigma(s) - s \in Q \text{ for all } s \in S\}$$ be its inertia group, and let $\varpi \in Q \setminus Q^2$ be a uniformizer at $Q$. For an ideal $J$ of $S$ let $v_Q(J)$ be the exponent of $Q$ in the prime factorization of $J$, and let $\mathfrak{D}_{S/R}$ be the different ideal of $S/R$ (the inverse of the trace dual of $S$). Then
--
--   $$v_Q(\mathfrak{D}_{S/R}) = \sum_{\sigma \in I_Q,\ \sigma \neq 1} v_Q\bigl((\varpi - \sigma\varpi)\bigr).$$
--
--   This is Hilbert's formula for the different. Writing $i_Q(\sigma) = v_Q(\sigma\varpi - \varpi)$, it reads $v_Q(\mathfrak{D}_{S/R}) = \sum_{\sigma \in I_Q \setminus \{1\}} i_Q(\sigma) = \sum_{u \ge 0} (|G_u| - 1)$, where $G_u$ are the lower ramification groups at $Q$ (Serre, *Local Fields*, Ch. IV, Prop. 4, which states it for complete discrete valuation rings). The statement here is global: there are no completions, and the different is the different of $S/R$ itself. Wild ramification is allowed; in the tame case every term is $1$ and the formula gives $v_Q(\mathfrak{D}_{S/R}) = e - 1$.
--
--   **Formalization Note**: `R`, `S`, `G` live in `Type`. The hypotheses are `[IsDedekindDomain R]`, `[IsDedekindDomain S]`, `[Algebra R S]`, `[Module.Finite R S]`, `[Module.IsTorsionFree R S]`, `[Group G]`, `[Finite G]`, `[MulSemiringAction G S]` and `[IsGaloisGroup G R S]`. `Q : IsDedekindDomain.HeightOneSpectrum S` with `[Finite (S ⧸ Q.asIdeal)]`, and the uniformizer is given by `h1 : ϖ ∈ Q.asIdeal` and `h2 : ϖ ∉ Q.asIdeal ^ 2`. $\mathfrak{D}_{S/R}$ is Mathlib's `differentIdeal R S`, and $I_Q$ is Mathlib's `Ideal.inertia G Q.asIdeal` (written `Q.asIdeal.inertia G`), the subgroup of those $\sigma$ with $\sigma s - s \in Q$ for all $s$. $v_Q(J)$ is `(Associates.mk Q.asIdeal).count (Associates.mk J).factors`, the multiplicity of $Q$ in the factorization of $J$ (the exponent Mathlib uses to define the $Q$-adic valuation `intValuation`). The sum is the finite sum `∑ᶠ σ ∈ (Q.asIdeal.inertia G : Set G) \ {1}, ...` over the finite set $I_Q \setminus \{1\}$, and $\sigma\varpi$ is `σ • ϖ`. Each $\varpi - \sigma\varpi$ with $\sigma \in I_Q \setminus \{1\}$ is nonzero, so every term is a genuine valuation. The hypotheses are not vacuous: for number fields $K \subseteq L$ with $L/K$ Galois, Mathlib infers `IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L)`, `Module.Finite`, `Module.IsTorsionFree` and finiteness of every residue field $\mathcal{O}_L/Q$, and every height-one prime has a uniformizer.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer 1979, Ch. IV, Sec. 1, Prop. 4 (Hilbert's formula for the different); global form via the inertia ring, which is unramified at Q, and the totally ramified extension of Dedekind domains above it

import Mathlib

set_option autoImplicit false

theorem IsDedekindDomain.HeightOneSpectrum.count_differentIdeal_eq_finsum_inertia
    {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (Q : IsDedekindDomain.HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]
    {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    (Associates.mk Q.asIdeal).count (Associates.mk (differentIdeal R S)).factors =
      ∑ᶠ σ ∈ (Q.asIdeal.inertia G : Set G) \ {1},
        (Associates.mk Q.asIdeal).count (Associates.mk (Ideal.span {ϖ - σ • ϖ})).factors := by
  sorry
