-- Prove2me | Theorems.Thm_NeronModelInfra_mem_vanishingIdeal_closure_of_forall_indexOne_algHom
-- name    : NeronModelInfra.mem_vanishingIdeal_closure_of_forall_indexOne_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/83285149-7bc1-522e-9f8e-0bd29c668ad3
-- title:
--   Index-one points detect the vanishing ideal of S̄
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation ring structure), let $X$ be a scheme, $f : X \to \operatorname{Spec} R$ a morphism, and $S \subseteq X$ a set of points subject to the hypothesis that for each $s \in S$ there exist a discrete valuation ring $R'$ (again a domain) and an $R$-algebra structure on $R'$ whose structure map is a local homomorphism and is an index-one extension, i.e. $\mathfrak m_R R' = \mathfrak m_{R'}$ and the residue field extension $k(R) \to k(R')$ is formally smooth, together with a morphism $x : \operatorname{Spec} R' \to X$ satisfying $x$ followed by $f$ equals $\operatorname{Spec}$ of $R \to R'$, such that $x$ sends the closed point of $R'$ to $s$. Let $U \subseteq X$ be an open subscheme which is affine. Equip $\Gamma(X, U)$ with the $R$-algebra structure obtained from the composite of the inverse of the canonical isomorphism $R \cong \Gamma(\operatorname{Spec} R, \top)$, the global sections map of $f$, and restriction from $X$ to $U$, and let $J \subseteq \Gamma(X, U)$ be the vanishing ideal of the set of primes $\mathfrak p_y$ corresponding under the affine open $U$ to those $y \in U$ lying in the closure of $S$ in $X$. The assertion is: for $g \in \Gamma(X, U)$, if for every discrete valuation ring $R''$ (a domain) that is an $R$-algebra by a local homomorphism and an index-one extension of $R$ in the above sense, and every $R$-algebra homomorphism $c : \Gamma(X, U) \to R''$ with $J \subseteq c^{-1}(\mathfrak m_{R''})$, one has $g \in c^{-1}(\mathfrak m_{R''})$, then $g \in J$.
--
--   This is the form in which property (N) — an element of the coordinate ring vanishing at every index-one $R$-algebra point that lies in $J$ already lies in $J$ — is recorded for the closure of a family of index-one specialisations; it belongs to the smoothening apparatus for weak Néron models. It is used in the construction of an antitone chain of closed sets all of whose points admit index-one charts, via [`NeronModelInfra.exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd`](thm.html#NeronModelInfra.exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_mem_vanishingIdeal_closure_of_forall_indexOne_algHom.lean

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem NeronModelInfra.mem_vanishingIdeal_closure_of_forall_indexOne_algHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (S : Set X)
    (hS : ∀ s ∈ S, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1 (IsLocalRing.closedPoint R') = s)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ closure S})
    ∀ g : Γ(X, U),
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : Γ(X, U) →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J := by sorry
