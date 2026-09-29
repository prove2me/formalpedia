-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_partialAction_compatible_maximal_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/9560ee51-a1c8-5248-b59d-81f42e2bcf04
-- title:
--   Maximal partial action by translation on a proper normal model
-- statement:
--   Let $k$ be an algebraically closed field, let $f \colon G \to \operatorname{Spec} k$ be a separated, quasi-compact, smooth morphism with $G$ connected, and let $L$ be a `RelativeGroupLaw` for $f$: a functorial group structure on the sets $\{\varphi \colon T \to G \mid \varphi \circ f = t\}$ of $T$-points of $G$ over each $t \colon T \to \operatorname{Spec} k$, with multiplication, unit and inverse satisfying associativity, both unit laws and left inverse, and with multiplication natural in $T$ along morphisms $\psi$ over $\operatorname{Spec} k$. Let $p \colon P \to \operatorname{Spec} k$ be proper with $P$ integral and every stalk $\mathcal{O}_{P,y}$ integrally closed, and let $\iota \colon V \to P$ be an open immersion with $\iota$ followed by $p$ equal to the inclusion of a non-empty open $V \subseteq G$ followed by $f$. Then there is a `PartialAction` $a$ of $f$ on $p$, that is a dense open $a.\mathrm{dom} \subseteq G \times_{\operatorname{Spec} k} P$ together with a morphism $a.\mathrm{hom} \colon a.\mathrm{dom} \to P$ over $\operatorname{Spec} k$ (compatible with the second projection followed by $p$), such that: (i) $a$ is compatible with left translation along $\iota$, i.e. for all $T$-points $\gamma$ of $G$ and $v, w$ of $V$ over the same $t$, if $w$ followed by the inclusion of $V$ equals $L.\mathrm{mul}\,t\,\gamma$ applied to $v$ followed by that inclusion, then the pair $(\gamma, v \circ \iota)$ has image inside $a.\mathrm{dom}$ and the resulting value $a.\mathrm{act}$ equals $w$ followed by $\iota$; (ii) $a$ is maximal, i.e. any open $U' \supseteq a.\mathrm{dom}$ carrying a morphism to $P$ whose restriction along $a.\mathrm{dom} \le U'$ is $a.\mathrm{hom}$ satisfies $U' = a.\mathrm{dom}$; and (iii) every point $z$ of $G \times_{\operatorname{Spec} k} P$ with $\operatorname{ringKrullDim} \mathcal{O}_z \le 1$ lies in $a.\mathrm{dom}$.
--
--   This is the classical construction, going back to Rosenlicht, of the birational action of a connected smooth group $G$ on a proper normal model $P$ of an open subset of $G$, induced by left translation, with largest possible domain of definition and defined at all points of codimension at most one. It is used in the study of the group law on Néron models, via [`GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one`](thm.html#GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_partialAction_compatible_maximal_of_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f) :
    ∃ a : PartialAction k f p, a.Compatible L V ι hι ∧ a.Maximal ∧
      ∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom := by sorry
