-- Prove2me | Theorems.Thm_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper
-- name    : GoodReductionJacobian.PartialAction.hom_base_notMem_of_snd_notMem_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/6e200585-e9db-5e3b-ad78-98b83b6f2f9f
-- title:
--   Partial action sends boundary points to boundary points
-- statement:
--   Let $k$ be an algebraically closed field and let $f : G \to \operatorname{Spec} k$ be a separated, quasi-compact, smooth morphism with $G$ connected, equipped with a relative group law $L$, i.e. for every $k$-scheme $t : T \to \operatorname{Spec} k$ a group structure (`mul`, `one`, `inv` with associativity, unit laws and left inverses) on the set $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of $T$-points of $G$ over $t$, the multiplication being natural with respect to precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} k$. Let $p : P \to \operatorname{Spec} k$ be separated and locally of finite type with $P$ integral, let $D \subseteq P$ be an open subscheme, $\tau : D \to G$ a proper morphism with $\tau$ followed by $f$ equal to the inclusion $D \hookrightarrow P$ followed by $p$, and let $V \subseteq G$ be a non-empty open subscheme together with an open immersion $\iota : V \to D$ such that $\iota$ followed by $\tau$ is the inclusion $V \hookrightarrow G$. Let $a$ be a partial action of $G$ on $P$: an open subscheme $\mathrm{dom}$ of $G \times_{\operatorname{Spec} k} P$ with dense underlying set, together with a morphism $a.\mathrm{hom} : \mathrm{dom} \to P$ over $\operatorname{Spec} k$, the structure morphism being the second projection composed with $p$. Assume $a$ is compatible with $L$ along $\iota$ followed by $D \hookrightarrow P$: for all $T$-points $\gamma$ of $G$ over $t$ and $v, w$ of $V$ over $V \hookrightarrow G \hookrightarrow \operatorname{Spec} k$, if $w$ pushed into $G$ equals $L.\mathrm{mul}\, t\, \gamma$ applied to $v$ pushed into $G$, then $a$ is defined at the pair $(\gamma, v\ \text{viewed in}\ P)$, meaning the range of the induced map to $G \times_{\operatorname{Spec} k} P$ lies in $\mathrm{dom}$, and `a.act` sends that pair to $w$ viewed in $P$. Then for every point $z$ of $\mathrm{dom}$ whose image under the second projection to $P$ does not lie in $D$, the point $a.\mathrm{hom}(z)$ also does not lie in $D$.
--
--   This is the step in Rosenlicht's treatment of group actions on complete models asserting that a birational group action carries the boundary $P \setminus D$ into itself wherever it is defined, $D$ being the open part of $P$ over which a proper comparison morphism $\tau$ to $G$ exists. It is used in the construction of Néron models by good reduction of Jacobians, namely by [`GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one`](thm.html#GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one), and its proof invokes the decomposition of $G$ supplied by [`GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper.lean

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

theorem GoodReductionJacobian.PartialAction.hom_base_notMem_of_snd_notMem_of_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ G) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι)
    (a : PartialAction k f p)
    (hc : a.Compatible L V (ι ≫ D.ι) (by rw [Category.assoc, ← hτ, ← Category.assoc, hτι]))
    (z : ↥(a.dom : Scheme.{u})) (hz : (pullback.snd f p).base (a.dom.ι.base z) ∉ (D : Set P)) :
    a.hom.base z ∉ (D : Set P) := by sorry
