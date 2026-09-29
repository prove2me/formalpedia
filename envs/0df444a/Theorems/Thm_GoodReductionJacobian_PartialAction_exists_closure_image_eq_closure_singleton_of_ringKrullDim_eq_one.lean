-- Prove2me | Theorems.Thm_GoodReductionJacobian_PartialAction_exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
-- name    : GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/53f73a4b-afbf-5201-a840-3ee915193662
-- title:
--   Rosenlicht's modification at a boundary point of codimension one
-- statement:
--   Let $k$ be an algebraically closed field and $f : G \to \operatorname{Spec} k$ a separated, quasi-compact, smooth morphism with $G$ connected, equipped with a relative group law $L$: a group structure, natural in $T$, on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$. Let $p : P \to \operatorname{Spec} k$ be proper with $P$ integral and every local ring $\mathcal{O}_{P,y}$ integrally closed; let $D \subseteq P$ be open with a proper morphism $\tau : D \to G$ satisfying $p \circ D.\iota = f \circ \tau$, and let $V \subseteq G$ be a non-empty open with an open immersion $\iota : V \to D$ such that $\tau \circ \iota$ is the inclusion $V \to G$. Finally let $w \in P$ with $w \notin D$ and $\dim \mathcal{O}_{P,w} = 1$. Then there are a scheme $P'$, a morphism $\pi : P' \to P$, a non-empty open $V' \subseteq G$, an open immersion $\iota' : V' \to P'$ with $p \circ \pi \circ \iota' = f \circ V'.\iota$, a partial action $a'$ of $G$ on $(P', p \circ \pi)$ — that is, a dense open $a'.\mathrm{dom}$ of $G \times_{\operatorname{Spec} k} P'$ together with $a'.\mathrm{hom} : a'.\mathrm{dom} \to P'$ commuting with the second projection over $\operatorname{Spec} k$ — and points $w', w'' \in P'$, such that: $P'$ is integral with all local rings integrally closed; $\pi$ is proper; $\operatorname{topologicalKrullDim} P' = \operatorname{topologicalKrullDim} G$; $a'$ is compatible with $L$ along $\iota'$, in the sense that for all $t : T \to \operatorname{Spec} k$, every $T$-point $\gamma$ of $G$ over $t$ and all $T$-points $v, w$ of $V$ over $t$ with $w$ (pushed into $G$) $= L.\mathrm{mul}\, t\, \gamma\, v$, the action $a'$ is defined at $(\gamma, \iota' \circ v)$ and sends it to $\iota' \circ w$; $a'.\mathrm{dom}$ is maximal among opens carrying a morphism to $P'$ restricting to $a'.\mathrm{hom}$; every point of $G \times_{\operatorname{Spec} k} P'$ whose local ring has Krull dimension $\le 1$ lies in $a'.\mathrm{dom}$; $\pi(w') = w$; $\dim \mathcal{O}_{P',w'} = \dim \mathcal{O}_{P',w''} = 1$; and the closure of the image under $a'.\mathrm{hom}$ of the set of points of $a'.\mathrm{dom}$ whose second projection lies in $\overline{\{w'\}}$ equals $\overline{\{w''\}}$.
--
--   This is Rosenlicht's modification step in the proof that a group law on a smooth connected $k$-scheme with a normal complete model extends: after replacing the model $P$ by a proper modification $P'$ of the same dimension, the $G$-translates of a one-dimensional boundary point sweep out the closure of a single one-dimensional point. It is used in the construction of a compatible partial action whose domain contains the identity section, towards the non-properness argument for the boundary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_PartialAction_exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one.lean

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

theorem GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ G) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι)
    (w : P) (hw : w ∉ (D : Set P)) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1) :
    ∃ (P' : Scheme.{u}) (π : P' ⟶ P) (V' : G.Opens)
      (ι' : (V' : Scheme.{u}) ⟶ P') (hι' : ι' ≫ π ≫ p = V'.ι ≫ f) (a' : PartialAction k f (π ≫ p))
      (w' w'' : P'),
      IsIntegral P' ∧ (∀ y : P', IsIntegrallyClosed (P'.presheaf.stalk y)) ∧ IsProper π ∧
      topologicalKrullDim ↥P' = topologicalKrullDim ↥G ∧
      Nonempty (V' : Scheme.{u}) ∧ IsOpenImmersion ι' ∧
      a'.Compatible L V' ι' hι' ∧ a'.Maximal ∧
      (∀ z : ↥(pullback f (π ≫ p)),
        ringKrullDim ((pullback f (π ≫ p)).presheaf.stalk z) ≤ 1 → z ∈ a'.dom) ∧
      π.base w' = w ∧
      ringKrullDim (P'.presheaf.stalk w') = 1 ∧ ringKrullDim (P'.presheaf.stalk w'') = 1 ∧
      closure (a'.hom.base '' ((a'.dom.ι ≫ pullback.snd f (π ≫ p)).base ⁻¹' closure {w'})) =
        closure {w''} := by sorry
