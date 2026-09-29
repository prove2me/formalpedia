-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_field
-- name    : GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/56babbb7-515a-5a28-ac0b-7a092601b917
-- title:
--   Multiplication by n>0 on an abelian variety is locally quasi-finite
-- statement:
--   Let $K$ be a field and let $f \colon A \to \operatorname{Spec} K$ be a morphism of schemes. Let $G$ be a relative group law for $f$ over $K$: for every scheme $T$ with a structure morphism $t \colon T \to \operatorname{Spec} K$ it provides a multiplication, a unit and an inverse on the set $\{\varphi \colon T \to A \mid \varphi$ followed by $f$ equals $t\}$ of $T$-points of $A$ over $K$, satisfying associativity, the two unit laws and left inverse, and compatible with base change along any $\psi \colon T' \to T$ over $\operatorname{Spec} K$ (composition with $\psi$ is a homomorphism). Assume `AbelianSchemePropertyBundle K f`, i.e. $f$ is smooth, $f$ is proper, each fibre $f^{-1}(s)$ of the underlying continuous map is connected, and $f$ admits some relative group law. Assume furthermore that $G$ is commutative, in the sense that for every $t$ and all $T$-points $x,y$ one has $G.\mathrm{mul}\,t\,x\,y = G.\mathrm{mul}\,t\,y\,x$. Let $n$ be a natural number with $n > 0$. Then the morphism $A \to A$ underlying the $n$-fold $G$-sum of the identity point $\mathrm{id}_A \in A(A)$, written `G.schemeNsmul n`, is locally quasi-finite.
--
--   This is the statement that multiplication by $n$ on an abelian variety over a field is an isogeny, in the quasi-finiteness half of that assertion (properness then upgrades it to finiteness). It is used in the treatment of fake elliptic curves, where finite flat surjectivity of maps determined by isogeny data is deduced from quasi-finiteness of $[n]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_field.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_field
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (G : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : 0 < n) :
    LocallyQuasiFinite (G.schemeNsmul n) := by sorry
