-- Prove2me | Theorems.Thm_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal
-- name    : GoodReductionJacobian.PartialAction.unitActs_and_assoc_of_compatible_of_maximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/9fa8c6a1-816c-5fdb-8db4-4ee7fdc99cff
-- title:
--   A maximal compatible partial action is a rational action
-- statement:
--   Let $k$ be an algebraically closed field, let $f\colon G\to\operatorname{Spec} k$ be separated, quasi-compact and smooth with $G$ connected, and let $L$ be a `RelativeGroupLaw` for $f$: a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of $T$-points of $G$ over $k$ (for $t\colon T\to\operatorname{Spec} k$), given by operations `mul`, `one`, `inv` satisfying associativity, the two unit laws and left inverses, with `mul` natural under base change along morphisms $\psi$ with $\psi\circ t=t'$. Let $p\colon P\to\operatorname{Spec} k$ be separated and locally of finite type with $P$ integral, let $V\subseteq G$ be an open subscheme whose underlying scheme is non-empty, and let $\iota\colon V\to P$ be an open immersion over $k$, i.e. $\iota$ followed by $p$ equals $V.\iota$ followed by $f$. Let $a$ be a `PartialAction` for $f$ and $p$: an open subscheme $\mathrm{dom}$ of $G\times_k P$ whose underlying set is dense, together with a morphism $\mathrm{hom}\colon\mathrm{dom}\to P$ over $k$ via the second projection. Assume (compatibility, `Compatible`) that for every $k$-scheme $T$, every $T$-point $\gamma$ of $G$ and all $T$-points $v,w$ of $V$ with $V.\iota\circ w=L.\mathrm{mul}\,t\,\gamma\,(V.\iota\circ v)$ in $G(T)$, the pair $(\gamma,\iota\circ v)$ lands in $\mathrm{dom}$ (the predicate `Defined`, i.e. the range of the induced map to $G\times_k P$ lies in $\mathrm{dom}$) and the resulting action value $a.\mathrm{act}\,\gamma\,(\iota\circ v)$ equals $\iota\circ w$; and (maximality, `Maximal`) that whenever an open $U'\supseteq\mathrm{dom}$ of $G\times_k P$ carries a morphism $h'\colon U'\to P$ restricting to $\mathrm{hom}$ on $\mathrm{dom}$, one has $U'=\mathrm{dom}$. Then both conclusions hold: `UnitActs`, that for every $T$-point $x$ of $P$ for which $(L.\mathrm{one}\,t,x)$ is defined one has $a.\mathrm{act}\,(L.\mathrm{one}\,t)\,x=x$; and `Assoc`, that for all $T$-points $\gamma,\delta$ of $G$ and $x$ of $P$ such that $\delta\cdot x$ and $\gamma\cdot(\delta\cdot x)$ are defined, the product $L.\mathrm{mul}\,t\,\gamma\,\delta$ is defined at $x$ and $a.\mathrm{act}\,\gamma\,(a.\mathrm{act}\,\delta\,x)=a.\mathrm{act}\,(L.\mathrm{mul}\,t\,\gamma\,\delta)\,x$.
--
--   This is the statement that a maximally defined partial operation of a connected smooth group scheme $G$ on an integral $k$-scheme $P$, which on a non-empty open $V\subseteq G$ embedded in $P$ agrees with left translation, is a rational action in the sense of Weil, Rosenlicht and Milne. It is used in the construction of a compatible partial action defined at the identity, which in turn feeds the good-reduction analysis of Jacobians via Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.PartialAction.unitActs_and_assoc_of_compatible_of_maximal
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι) (hm : a.Maximal) :
    a.UnitActs L ∧ a.Assoc L := by sorry
