-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/e66db9fc-d859-5e37-9e1d-bfdea8c85002
-- title:
--   Rank of finite part of n-torsion read on special fibre
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f\colon X\to\operatorname{Spec}R$ a morphism, and $L$ a `RelativeGroupLaw` on $f$: a group structure, natural in $T$, on the sets $\{\varphi\colon T\to X \mid \varphi\text{ followed by }f = t\}$ of $T$-points over each $t\colon T\to\operatorname{Spec}R$, with multiplication, unit and inverse satisfying associativity, both unit laws, left inversion and naturality of multiplication along any $\psi\colon T'\to T$ over $\operatorname{Spec}R$. Let $R'$ be a commutative local ring, $\iota\colon\operatorname{Spec}R'\to\operatorname{Spec}R$ a morphism, $k$ a field and $\pi\colon R'\to k$ a ring homomorphism whose kernel is exactly the maximal ideal of $R'$, and put $c=\operatorname{Spec}(\pi)$ followed by $\iota$. Fix $n\in\mathbb{N}$ and a commutative $R'$-algebra $A$ that is finite and free as an $R'$-module. Here `L.baseChange \iota` is the induced group law on $X\times_{\operatorname{Spec}R}\operatorname{Spec}R'$ with structure morphism the second projection, `schemeKer n` is the fibre product of the $n$-fold multiplication endomorphism `schemeNsmul n` of the identity point with the unit section, and `schemeKerStr n` its structure morphism to the base. Assume given $j\colon\operatorname{Spec}A\to(L.\mathrm{baseChange}\,\iota).\mathrm{schemeKer}\,n$ which is a morphism of $R'$-schemes ($j$ followed by `schemeKerStr n` equals $\operatorname{Spec}$ of $R'\to A$), is both an open and a closed immersion, and whose image on points contains every point of the kernel lying over the closed point of $R'$. Then the structure morphism $(L.\mathrm{baseChange}\,c).\mathrm{schemeKerStr}\,n$ of the kernel of $[n]$ on $X\times_{\operatorname{Spec}R}\operatorname{Spec}k$ is a finite morphism, and $\operatorname{rank}_{R'}A$ equals the dimension over $k$ of the global sections $\Gamma((L.\mathrm{baseChange}\,c).\mathrm{schemeKer}\,n,\top)$, for the $k$-algebra structure induced by that structure morphism.
--
--   This is the statement that kernels of multiplication by $n$ commute with base change and that the rank of the finite part of the $n$-torsion over a local base can be read off on the special fibre, in the form used for Néron models of Jacobians. It is invoked in the computation of the rank of the finite part of the $n$-torsion of a Néron object at $p$ and in the comparison of heights of Raynaud quotients with level-torsion heights.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range
    {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {R' : Type} [CommRing R'] [IsLocalRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {k : Type} [Field k] (π : R' →+* k) (hker : ∀ x : R', π x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R')
    (c : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (hc : Spec.map (CommRingCat.ofHom π) ≫ ι = c)
    (n : ℕ) (A : Type) [CommRing A] [Algebra R' A] [Module.Finite R' A] [Module.Free R' A]
    (j : Spec (CommRingCat.of A) ⟶ (L.baseChange ι).schemeKer n)
    (hj : j ≫ (L.baseChange ι).schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap R' A)))
    (hjo : IsOpenImmersion j) (hjc : IsClosedImmersion j)
    (hcov : ∀ x : ↥((L.baseChange ι).schemeKer n),
      ((L.baseChange ι).schemeKerStr n).base x = IsLocalRing.closedPoint R' → x ∈ Set.range j.base) :
    IsFinite ((L.baseChange c).schemeKerStr n) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((L.baseChange c).schemeKerStr n) ⊤
     Module.finrank R' A = Module.finrank k Γ((L.baseChange c).schemeKer n, ⊤)) := by sorry
