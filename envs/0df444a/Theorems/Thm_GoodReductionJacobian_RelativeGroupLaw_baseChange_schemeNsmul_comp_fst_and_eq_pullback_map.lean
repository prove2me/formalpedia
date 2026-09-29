-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
-- name    : GoodReductionJacobian.RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/595d569b-654d-5ce3-8c93-190da72fda5f
-- title:
--   Multiplication by n commutes with base change of a relative group law
-- statement:
--   Let $R$ and $R'$ be commutative rings and let $\iota\colon\operatorname{Spec}R'\to\operatorname{Spec}R$ be a morphism of affine schemes; let $f\colon A\to\operatorname{Spec}R$ be a morphism of schemes and let $G$ be a relative group law on $f$, that is, a functorial group structure (multiplication, unit, inverse, associativity, unit laws, left inverse law, and naturality of the multiplication along morphisms of test schemes over $\operatorname{Spec}R$) on the sets $\{\varphi\colon T\to A \mid \varphi\circ f = t\}$ of $T$-points of $A$ over $t\colon T\to\operatorname{Spec}R$. Let $n$ be a natural number. Write $[n]_G\colon A\to A$ for `G.schemeNsmul n`, the underlying morphism of the $n$-fold $G$-sum of the universal point $\mathrm{id}_A$ (an empty sum being the unit section), and let `G.baseChange ι` be the induced relative group law on $\operatorname{pr}_2\colon A\times_{\operatorname{Spec}R}\operatorname{Spec}R'\to\operatorname{Spec}R'$, obtained by transporting the group structure on points through the pullback bijection. The conclusion is the conjunction of three assertions: $[n]_{G_{R'}}$ followed by $\operatorname{pr}_1$ equals $\operatorname{pr}_1$ followed by $[n]_G$; $[n]_{G_{R'}}$ followed by $\operatorname{pr}_2$ equals $\operatorname{pr}_2$; and $[n]_{G_{R'}}$ coincides with the morphism of pullbacks induced by $[n]_G$ on $A$ and the identity of $\operatorname{Spec}R'$ (using $[n]_G$ followed by $f$ equal to $f$).
--
--   This is the statement that multiplication by $n$ on a relative group scheme is compatible with base change, in the functor-of-points formulation used throughout this development. The third clause identifies $[n]$ on the base change with the fibre product of $[n]$ with $\operatorname{Spec}R'$, which is what allows properties of $[n]$ stable under base change (finiteness, flatness, surjectivity) to be transported from $G$ to base changes and fibres; it is cited in the analysis of kernels of $[n]$, of torsion characters, and of split tori over a Henselian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) :
    (G.baseChange ι).schemeNsmul n ≫ pullback.fst f ι = pullback.fst f ι ≫ G.schemeNsmul n ∧
    (G.baseChange ι).schemeNsmul n ≫ pullback.snd f ι = pullback.snd f ι ∧
    (G.baseChange ι).schemeNsmul n =
      pullback.map f ι f ι (G.schemeNsmul n) (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, G.schemeNsmul_over]) (by rw [Category.comp_id, Category.id_comp]) := by sorry
