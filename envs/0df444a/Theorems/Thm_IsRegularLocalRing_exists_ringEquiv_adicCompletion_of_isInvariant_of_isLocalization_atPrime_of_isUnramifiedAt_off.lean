-- Prove2me | Theorems.Thm_IsRegularLocalRing_exists_ringEquiv_adicCompletion_of_isInvariant_of_isLocalization_atPrime_of_isUnramifiedAt_off
-- name    : IsRegularLocalRing.exists_ringEquiv_adicCompletion_of_isInvariant_of_isLocalization_atPrime_of_isUnramifiedAt_off
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/b36134ed-b4fc-5cbd-82b5-dd8ec351639a
-- title:
--   Abhyankar's lemma at a tame point: completion of S_y
-- statement:
--   Let $A_2 \to A_1$ be a module-finite extension of Noetherian commutative rings with $A_1$ a domain and $A_2 \to A_1$ injective, and let $G$ be a finite group acting faithfully on $A_1$ by ring automorphisms commuting with the $A_2$-action, such that every $G$-invariant element of $A_1$ comes from $A_2$. Let $y \subset A_1$ be a maximal ideal with $y \cap A_2 = \mathfrak p$ for a prime $\mathfrak p \subset A_2$, let $e > 0$ be a natural number such that the inertia subgroup $y.\mathrm{inertia}\,G$ has cardinality $e$ and is cyclic, let $\mathfrak Q_0 \subseteq \mathfrak p$ be a prime of $A_2$ and $\varpi \in A_2$. Let $O$ be a Noetherian local $A_2$-algebra which is a localisation of $A_2$ at $\mathfrak p$, and $s \in O$ with $\mathfrak Q_0 O = (s)$, $\mathfrak m_O = (\varpi, s)$, $\operatorname{ringKrullDim} O = 2$ and $e$ a unit in $O$. Let $S$ be a local $A_1$-algebra which is a localisation of $A_1$ at $y$, and assume the $\mathfrak m_S$-adic completion $\widehat S$ is a domain and integrally closed. Assume further that $A_1$ is unramified over $A_2$ at every prime $\mathfrak Q \subseteq y$ of height $1$ with $\mathfrak Q \cap A_2 \neq \mathfrak Q_0$, and that the residue extension $A_2/\mathfrak p \to A_1/y$ (formed from the inclusion $\mathfrak p \subseteq y \cap A_2$) is separable. Then there exist a regular local ring $R'$ and elements $\varpi', \tau \in R'$ with $\mathfrak m_{R'} = (\varpi', \tau)$ and $\operatorname{ringKrullDim} R' = 2$, together with a ring isomorphism $\iota : \widehat S \xrightarrow{\sim} \widehat{R'}$ between the respective maximal-adic completions carrying the image of $\varpi$ in $\widehat S$ to the image of $\varpi'$ in $\widehat{R'}$.
--
--   This is the tame, two-dimensional form of Abhyankar's lemma, packaged so that the completion of the local ring of $A_1$ at a maximal ideal $y$ is identified with the completion of a regular two-dimensional local ring in which the chosen function $\varpi$ becomes one of the two regular parameters. It is the at-prime version of the corresponding statement over a regular local base, and it feeds the regularity analysis of fibres of the full-level modular curve at points where the level automorphisms act with nontrivial (tame, cyclic) inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_exists_ringEquiv_adicCompletion_of_isInvariant_of_isLocalization_atPrime_of_isUnramifiedAt_off.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsRegularLocalRing.exists_ringEquiv_adicCompletion_of_isInvariant_of_isLocalization_atPrime_of_isUnramifiedAt_off
    {A₂ A₁ : Type} [CommRing A₂] [CommRing A₁] [IsNoetherianRing A₂] [IsNoetherianRing A₁] [IsDomain A₁]
    [Algebra A₂ A₁] [Module.Finite A₂ A₁] [FaithfulSMul A₂ A₁]
    {G : Type} [Group G] [Fintype G] [MulSemiringAction G A₁] [SMulCommClass G A₂ A₁] [FaithfulSMul G A₁]
    [Algebra.IsInvariant A₂ A₁ G]
    (y : Ideal A₁) [y.IsMaximal] (𝔭 : Ideal A₂) [𝔭.IsPrime] (h𝔭 : y.comap (algebraMap A₂ A₁) = 𝔭)
    (e : ℕ) (he : 0 < e)
    (hIy : Nat.card ↥(y.inertia G) = e) (hIcyc : IsCyclic ↥(y.inertia G))
    (𝔔₀ : Ideal A₂) [𝔔₀.IsPrime] (h𝔔₀ : 𝔔₀ ≤ 𝔭) (ϖ : A₂)
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [Algebra A₂ O] [IsLocalization.AtPrime O 𝔭]
    (s : O) (hsO : 𝔔₀.map (algebraMap A₂ O) = Ideal.span {s})
    (hmaxO : maximalIdeal O = Ideal.span {algebraMap A₂ O ϖ, s}) (hdimO : ringKrullDim O = 2)
    (heO : IsUnit (e : O))
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra A₁ S] [IsLocalization.AtPrime S y]
    (hSdom : IsDomain (AdicCompletion (maximalIdeal S) S))
    (hSnorm : IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S))

    (hunr : ∀ (𝔔 : Ideal A₁) [𝔔.IsPrime], 𝔔 ≤ y → 𝔔.height = 1 → 𝔔.comap (algebraMap A₂ A₁) ≠ 𝔔₀ →
      Algebra.IsUnramifiedAt A₂ 𝔔)

    (hsep : ∀ h : 𝔭 ≤ y.comap (algebraMap A₂ A₁),
      letI : Algebra (A₂ ⧸ 𝔭) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap h
      Algebra.IsSeparable (A₂ ⧸ 𝔭) (A₁ ⧸ y)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsRegularLocalRing R') (ϖ' τ : R')
      (_ : maximalIdeal R' = Ideal.span {ϖ', τ}) (_ : ringKrullDim R' = 2)
      (ι : AdicCompletion (maximalIdeal S) S ≃+* AdicCompletion (maximalIdeal R') R'),
      ι (algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap A₁ S (algebraMap A₂ A₁ ϖ))) =
        algebraMap R' (AdicCompletion (maximalIdeal R') R') ϖ' := by sorry
