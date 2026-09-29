-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_away_relativeGroupLaw_baseChange_one_eq_of_isNoetherianRing_of_isClopen
-- name    : GoodReductionJacobian.exists_away_relativeGroupLaw_baseChange_one_eq_of_isNoetherianRing_of_isClopen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/bec9f1df-31f2-5753-ae43-800748124a87
-- title:
--   Local group law with prescribed unit over a Noetherian base
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $f : A \to \operatorname{Spec} R$ be a morphism of schemes that is smooth and proper. Assume given $N \in \mathbb{N}$ and a closed immersion $\iota$ of $A$ into $\operatorname{Proj}$ of the graded ring of polynomials in $N+1$ variables over $R$, compatible with the bases in the sense that $\iota$ followed by the structure morphism `ProjSpace.π R N` equals $f$; a section $e$, i.e. a morphism $\operatorname{Spec} R \to A$ with $e$ followed by $f$ equal to the identity; and a subset $W \subseteq \operatorname{Spec} R$ that is clopen, such that for every $s \in W$ the fibre $f^{-1}(s)$ is connected (nonempty and not a disjoint union of two nonempty open pieces), and such that for every algebraically closed field $k$ and every morphism $\sigma : \operatorname{Spec} k \to \operatorname{Spec} R$ whose image lies in $W$ the second projection $A \times_{\operatorname{Spec} R} \operatorname{Spec} k \to \operatorname{Spec} k$ satisfies `AbelianSchemePropertyBundle`: it is smooth and proper, all its fibres are connected, and it admits a relative group law. Then for every $s \in W$ there exists $r \in R$ lying outside the prime ideal corresponding to $s$ and a `RelativeGroupLaw` on the base change $A \times_{\operatorname{Spec} R} \operatorname{Spec} R[1/r] \to \operatorname{Spec} R[1/r]$ along $\operatorname{Spec}$ of $R \to R[1/r] =$ `Localization.Away r` — that is, a multiplication, unit and inverse on the sets of $T$-points over $\operatorname{Spec} R[1/r]$, for all $R[1/r]$-schemes $T$, satisfying associativity, the two unit laws, left invertibility, and naturality of the multiplication under base change along morphisms $T' \to T$ over $\operatorname{Spec} R[1/r]$ — whose unit section over $T = \operatorname{Spec} R[1/r]$ is, as a morphism, the canonical map into the fibre product determined by $\operatorname{Spec} R[1/r] \to \operatorname{Spec} R$ followed by $e$ and by the identity, i.e. the base change of the given section $e$.
--
--   This is the Zariski-local existence half of the statement that a smooth proper projective scheme with connected abelian geometric fibres over a clopen part of the base carries a group law with unit the given section, in the form needed for the Jacobian of a modular curve: the group law is produced only after inverting a single element $r$ not vanishing at the chosen point $s$. It feeds the global statement [`GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing`](thm.html#GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_away_relativeGroupLaw_baseChange_one_eq_of_isNoetherianRing_of_isClopen.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.exists_away_relativeGroupLaw_baseChange_one_eq_of_isNoetherianRing_of_isClopen
    {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hs : Smooth f) (hp : IsProper f)
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (W : Set ↥(Spec (CommRingCat.of R))) (hW : IsClopen W)
    (hc : ∀ s : Spec (CommRingCat.of R), s ∈ W → _root_.IsConnected (f.base ⁻¹' {s}))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Set.range s.base ⊆ W → AbelianSchemePropertyBundle k (pullback.snd f s))
    (s : Spec (CommRingCat.of R)) (hsW : s ∈ W) :
    ∃ (r : R), r ∉ s.asIdeal ∧
      ∃ L : RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))),
        (L.one (𝟙 _)).1 = pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ e.1) (𝟙 _)
          (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) := by sorry
