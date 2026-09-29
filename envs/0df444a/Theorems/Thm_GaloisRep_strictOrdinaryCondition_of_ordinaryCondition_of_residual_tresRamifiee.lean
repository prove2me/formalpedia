-- Prove2me | Theorems.Thm_GaloisRep_strictOrdinaryCondition_of_ordinaryCondition_of_residual_tresRamifiee
-- name    : GaloisRep.strictOrdinaryCondition_of_ordinaryCondition_of_residual_tresRamifiee
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/7f200bd3-0589-5d5e-9e96-533af54788fe
-- title:
--   Ordinary deformations of a très ramifiée residual representation are strict
-- statement:
--   Fix a commutative ring $\mathcal O$, an odd prime $p$ (so $p \neq 2$), a finite set $S$ of natural numbers, and a Noetherian local $\mathcal O$-algebra $A$ whose residue field is finite. Let $\rho$ be an adic Galois representation over $A$, that is, a free $A$-module $V$ of rank $2$, finite over $A$, with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_A(V)$ that is continuous in the sense that for each $n$ some finite subextension $L/\mathbb Q$ has all elements fixing $L$ acting trivially modulo $\mathfrak m_A^n V$. Assume: (i) $\rho$ satisfies the ordinary condition of type $(\mathcal O,p,S)$, i.e. $\rho$ has cyclotomic determinant ($p \in \mathfrak m_A$, and $\det \rho(\sigma) - a \in (p^n)$ whenever $\sigma$ raises all $p^n$-th roots of unity to the $a$-th power), $\rho$ satisfies the predicate `IsOrdinaryAt` at $p$ — which for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p \in P^{\mathrm{nonunits}}$ furnishes a submodule $L$ of $V$ of the form $A \cdot b_0$ for some basis $b$ of $V$ indexed by $\mathrm{Fin}\,2$, stable under the decomposition group of $P$ over $\mathbb Q$ and with the inertia subgroup acting trivially on $V/L$ — and $\rho$ is unramified at every prime $q \notin S$ (every inertia element at every place over $q$ acts as the identity); (ii) the residual representation $\bar\rho = k \otimes_A V$, viewed as an adic representation over the residue field $k$ of $A$, is strictly ordinary at $p$; (iii) $\bar\rho$ is très ramifiée at $p$ in the unit–Kummer form: for every $n$ and all families $u, \beta : \mathrm{Fin}\,n \to \overline{\mathbb Q}$ with each $u_i$ of valuation $1$ at the place [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) and fixed by its inertia group, and $\beta_i^p = u_i$, there is an inertia element $\sigma$ at that place fixing every $p$-th root of unity and every $\beta_i$ with $\bar\rho(\sigma) \neq 1$. Then $\rho$ satisfies the strict ordinary condition of type $(\mathcal O,p,S)$: cyclotomic determinant, unramified outside $S$, and strictly ordinary at $p$, meaning that $p \in \mathfrak m_A$ and for every place $P$ over $p$ there is a line $L = A \cdot b_0$ as above, stable under decomposition, with inertia trivial on $V/L$, and such that every decomposition element $\sigma$ acts on $L$ by a scalar $x$ and on $V/L$ by a scalar $z$ with $x - a z \in (p^n)$ whenever $\sigma$ raises all $p^n$-th roots of unity to the $a$-th power.
--
--   This is the assertion that an ordinary (Selmer) deformation of a strictly ordinary, très ramifiée residual representation is automatically strictly ordinary, the variant of Wiles' Proposition 1.1(ii) in which the "not finite flat" condition at $p$ is replaced by Serre's très ramifiée condition in Kummer-theoretic form. It is used in the construction of the patching data for the modularity lifting theorems applied in the Fermat argument, in the cases distinguished by divisibility conditions on the level and on the exponents at $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_strictOrdinaryCondition_of_ordinaryCondition_of_residual_tresRamifiee.lean

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.strictOrdinaryCondition_of_ordinaryCondition_of_residual_tresRamifiee
    (𝒪 : Type) [CommRing 𝒪] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset ℕ)
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra 𝒪 A]
    [Finite (IsLocalRing.ResidueField A)]
    (ρ : GaloisRepAdic A)
    (hord : GaloisRep.ordinaryCondition 𝒪 p S ρ)
    (hstrbar : (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsStrictOrdinaryAt p)
    (htres : ∀ (n : ℕ) (u β : Fin n → AlgebraicClosure ℚ),
        (∀ i, (padicPlace p).valuation (u i) = 1) →
        (∀ i, ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, σ (u i) = u i) →
        (∀ i, β i ^ p = u i) →
        ∃ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ) ∧ (∀ i, σ (β i) = β i) ∧
            ρ.residual.ρ σ ≠ 1) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S ρ := by sorry
