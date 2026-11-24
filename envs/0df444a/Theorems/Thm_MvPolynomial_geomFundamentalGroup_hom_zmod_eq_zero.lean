-- Prove2me | Theorems.Thm_MvPolynomial_geomFundamentalGroup_hom_zmod_eq_zero
-- name    : MvPolynomial.geomFundamentalGroup_hom_zmod_eq_zero
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-24T04:50:13.592414+00:00
-- url     : https://prove2.me/theorems/c32113da-81ce-4c72-9e2e-4a5ee8074057
-- title:
--   Prime-to-$p$ characters of the geometric fundamental group of affine space over a finite field vanish: $H^1(\mathbb{A}^n_{\overline{\mathbb{F}}_q}, \mathbb{Z}/N) = 0$ for $p \nmid N$
-- statement:
--   Let $\mathbb{F}$ be a finite field of characteristic $p$, let $n \ge 0$, let $A = \mathbb{F}[x_1, \dots, x_n]$ be the coordinate ring of affine space $\mathbb{A}^n_{\mathbb{F}}$, and let $K$ be its fraction field. Fix an algebraic closure $\overline{K}$ and let $K_U \subset \overline{K}$ be the compositum of all finite Galois extensions $L/K$ in $\overline{K}$ that are unramified over $A$: for every prime $\mathfrak{P}$ of the integral closure $A_L$ of $A$ in $L$, the only $\sigma \in \mathrm{Gal}(L/K)$ with $\sigma(b) \equiv b \pmod{\mathfrak{P}}$ for all $b \in A_L$ is $\sigma = 1$. Thus $\mathrm{Gal}(K_U/K)$, with its Krull topology, is the étale fundamental group $\pi_1(\mathbb{A}^n_{\mathbb{F}})$. Let
--
--   $$\pi_1^{\mathrm{geo}} = \{\sigma \in \mathrm{Gal}(K_U/K) : \sigma(x) = x \text{ for every } x \in K_U \text{ with } x^{p^m} = x \text{ for some } m \ge 1\}$$
--
--   be the subgroup fixing all constants $\overline{\mathbb{F}}_p \cap K_U$. Since constant field extensions are unramified, $K\overline{\mathbb{F}}_p \subseteq K_U$ and $\pi_1^{\mathrm{geo}} = \mathrm{Gal}(K_U / K\overline{\mathbb{F}}_p)$ is the geometric fundamental group $\pi_1(\mathbb{A}^n_{\overline{\mathbb{F}}_q})$, the kernel of $\pi_1(\mathbb{A}^n_{\mathbb{F}}) \to \mathrm{Gal}(\overline{\mathbb{F}}/\mathbb{F})$.
--
--   Then for every integer $N \ge 1$ prime to $p$, every continuous (that is, locally constant) homomorphism $c : \pi_1^{\mathrm{geo}} \to \mathbb{Z}/N\mathbb{Z}$ is zero. Equivalently,
--
--   $$H^1(\mathbb{A}^n_{\overline{\mathbb{F}}_q}, \mathbb{Z}/N\mathbb{Z}) = \mathrm{Hom}_{\mathrm{cont}}(\pi_1^{\mathrm{geo}}, \mathbb{Z}/N\mathbb{Z}) = 0 \qquad (p \nmid N):$$
--
--   affine space over $\overline{\mathbb{F}}_q$ has no nontrivial abelian étale covering of degree prime to $p$.
--
--   In characteristic $p$ the fundamental group of $\mathbb{A}^n$ is enormous (Artin–Schreier coverings $y^p - y = f$ give infinitely many independent $\mathbb{Z}/p$ quotients, already for $n = 1$), so the hypothesis $p \nmid N$ is essential. The prime-to-$p$ statement is Kummer theory: $\mu_N \subset \overline{\mathbb{F}}_p$, so a cyclic covering of degree $N$ is obtained by adjoining an $N$-th root of a function $a \in K$; unramifiedness forces every valuation of $a$ at a height-one prime of the UFD $\overline{\mathbb{F}}_p[x_1, \dots, x_n]$ to be divisible by $N$, so $a$ is a unit times an $N$-th power, and the units are the constants, which are $N$-th powers in $\overline{\mathbb{F}}_p$. With $\ell \ne p$ this gives $H^1(\mathbb{A}^n_{\overline{\mathbb{F}}_q}, \mathbb{Z}/\ell^k) = 0$ for all $k$, hence $H^1(\mathbb{A}^n_{\overline{\mathbb{F}}_q}, \mathbb{Z}_\ell) = 0$, the vanishing used for affine spaces in $\ell$-adic cohomology over finite fields.
--
--   **Formalization Note**: $A$ is `MvPolynomial (Fin n) F` with `[Finite F]`, and $K$ is any field with `[IsFractionRing (MvPolynomial (Fin n) F) K]` and `[CharP K p]`, `p` prime. $\overline{K}$ is `AlgebraicClosure K` and $K_U$ is a variable `KU : IntermediateField K (AlgebraicClosure K)` with defining equation `hKU`, an `iSup` over the intermediate fields `L` with `FiniteDimensional K L`, `IsGalois K L` and the unramifiedness condition; $A_L$ is `integralClosure (MvPolynomial (Fin n) F) L` and the congruence $\sigma(b) \equiv b \pmod{\mathfrak{P}}$ is written elementwise as `∃ c ∈ P, (c : L) = σ b - b`. $\mathrm{Gal}(K_U/K)$ is `KU ≃ₐ[K] KU` with Mathlib's Krull topology instance, and $\pi_1^{\mathrm{geo}}$ is a variable `G : Subgroup (KU ≃ₐ[K] KU)` with membership criterion `hG`. Continuity into the discrete group $\mathbb{Z}/N\mathbb{Z}$ (`ZMod N`) is `IsLocallyConstant c` on the subspace `G`, the homomorphism property is `c (g * h) = c g + c h`, $N \ge 1$ is `[NeZero N]` and $p \nmid N$ is `Nat.Coprime p N`. Since the coefficients $\mathbb{Z}/N\mathbb{Z}$ carry the trivial action, continuous homomorphisms are exactly the continuous 1-cocycles and the 1-coboundaries are zero, so the conclusion `c = 0` is the vanishing of $H^1$. The hypotheses are satisfiable for every $n$ (take $\mathbb{F} = \mathbb{Z}/p$ and `K = FractionRing (MvPolynomial (Fin n) F)`; `KU` and `G` are determined by `hKU` and `hG`), and for $n \ge 1$ the group $\pi_1^{\mathrm{geo}}$ is nontrivial (Artin–Schreier coverings), so the statement is not vacuous.
-- source:
--   A. Grothendieck, Revêtements étales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Exposés V and IX (the étale fundamental group and its geometric part); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapters I and III (fundamental group, Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Rapport »

import Mathlib

set_option autoImplicit false

theorem MvPolynomial.geomFundamentalGroup_hom_zmod_eq_zero
    (F : Type) [Field F] [Finite F] (n : ℕ) (K : Type) [Field K]
    [Algebra (MvPolynomial (Fin n) F) K] [IsFractionRing (MvPolynomial (Fin n) F) K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (KU : IntermediateField K (AlgebraicClosure K))
    (hKU : KU = ⨆ L : {L : IntermediateField K (AlgebraicClosure K) //
        FiniteDimensional K L ∧ IsGalois K L ∧
        ∀ P : Ideal (integralClosure (MvPolynomial (Fin n) F) L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
          (∀ b : integralClosure (MvPolynomial (Fin n) F) L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1}, L.1)
    (G : Subgroup (KU ≃ₐ[K] KU))
    (hG : ∀ σ : KU ≃ₐ[K] KU, σ ∈ G ↔ ∀ x : KU, (∃ m : ℕ, 0 < m ∧ x ^ p ^ m = x) → σ x = x)
    (N : ℕ) [NeZero N] (hpN : Nat.Coprime p N)
    (c : G → ZMod N) (hc : IsLocallyConstant c) (hadd : ∀ g h : G, c (g * h) = c g + c h) :
    c = 0 := by sorry
