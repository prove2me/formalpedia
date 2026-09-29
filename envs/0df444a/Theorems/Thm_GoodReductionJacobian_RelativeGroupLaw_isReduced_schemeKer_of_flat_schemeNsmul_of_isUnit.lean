-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/612bf34e-54ad-5eb9-94ab-73c039bf9216
-- title:
--   Reducedness of ker[n] when [n] is flat and n invertible
-- statement:
--   Let $R$ be a commutative domain, $K$ a field which is an $R$-algebra, and suppose the structure map $R \to K$ is injective. Let $A$ be a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism that is locally of finite type, and let $G$ be a relative group law on $f$: for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set $\{\varphi \colon T \to A : \varphi \text{ followed by } f = t\}$ of $T$-points of $A$ over $t$, satisfying associativity, the two unit laws and left inverses, and compatible with precomposition along any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume further that each of these multiplications is commutative, as expressed by `hcomm`. Let $n$ be a natural number whose image in $K$ is a unit, and assume that the morphism $G$`.schemeNsmul` $n \colon A \to A$ — the underlying morphism of the $n$-fold $G$-power of the tautological point $\mathrm{id}_A$ in the group of $A$-points of $A$ over $f$ — is flat. Then the scheme $G$`.schemeKer` $n$, defined as the fibre product of $G$`.schemeNsmul` $n \colon A \to A$ with the unit section $\operatorname{Spec} R \to A$ attached by $G$ to $\mathrm{id}_{\operatorname{Spec} R}$, is reduced.
--
--   This is the statement that the $n$-torsion subscheme of a commutative group scheme over a domain is reduced as soon as multiplication by $n$ is flat and $n$ is invertible on a field extension of the base, the generic-fibre hypothesis entering through an arbitrary injective map $R \to K$ rather than through the fraction field; no smoothness or separatedness of $f$ is assumed. It is used when level structures of order invertible on the base are compared with étale closed subschemes of torsion, in the Čerednik–Drinfeld setting and in the construction of Drinfeld bases on Weierstrass curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isReduced_schemeKer_of_flat_schemeNsmul_of_isUnit
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hRK : Function.Injective (algebraMap R K))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : K)) [Flat (G.schemeNsmul n)] :
    IsReduced (G.schemeKer n) := by sorry
