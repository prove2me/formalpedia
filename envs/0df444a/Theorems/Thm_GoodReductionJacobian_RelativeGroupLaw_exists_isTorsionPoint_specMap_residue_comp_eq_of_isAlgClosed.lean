-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/60403435-c5b6-5515-8849-57b2c929aa9d
-- title:
--   Lifting torsion points from the residue field to a henselian valuation ring
-- statement:
--   Let $R$ be a commutative ring, $K$ an algebraically closed field and $A \subseteq K$ a valuation subring which is henselian as a local ring, with residue field $\kappa = A/\mathfrak m_A$, and let $\iota : \operatorname{Spec} A \to \operatorname{Spec} R$ be a morphism of schemes. Let $f : X \to \operatorname{Spec} R$ be separated and locally of finite type, and let $L$ be a relative group law on $f$: a group structure, functorial in $T$, on each set $\{\varphi : T \to X \mid \varphi \text{ followed by } f = t\}$ of sections over a morphism $t : T \to \operatorname{Spec} R$, with multiplication compatible with precomposition in $T$. Assume $L$ is commutative on sections over every base $t$, and fix $n \in \mathbb N$. Write $L_A$ for the group law obtained by base change along $\iota$ on $\operatorname{pullback.snd} f\,\iota : X \times_{\operatorname{Spec} R} \operatorname{Spec} A \to \operatorname{Spec} A$, and assume that the structure morphism to $\operatorname{Spec} A$ of its $n$-kernel — the fibre product of the $n$-fold multiplication endomorphism of $X_A$ and the unit section — is locally quasi-finite, quasi-compact and flat. Then for every section $y$ of $f$ over $\operatorname{Spec}\kappa \to \operatorname{Spec} A \xrightarrow{\iota} \operatorname{Spec} R$ (the first map induced by the residue map) whose $n$-fold $L$-multiple is the unit section, there exists a section $s$ of $f$ over $\iota$ whose $n$-fold $L$-multiple is the unit section and whose restriction along $\operatorname{Spec}$ of the residue map equals $y$.
--
--   This is the statement that $n$-torsion points of the special fibre of a smooth-enough commutative group scheme over a henselian valuation ring with algebraically closed fraction field lift to $n$-torsion sections over the ring itself. It is used in the study of the Néron model of the Jacobian of a modular curve at $p$, to produce integral torsion sections reducing to prescribed points of the fibre at a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
    {R : Type} [CommRing R] {K : Type} [Field K] [IsAlgClosed K] (A : ValuationSubring K) [HenselianLocalRing ↥A]
    (ι : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (n : ℕ)
    [LocallyQuasiFinite ((L.baseChange ι).schemeKerStr n)] [QuasiCompact ((L.baseChange ι).schemeKerStr n)]
    [Flat ((L.baseChange ι).schemeKerStr n)]
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ ι) f)
    (hy : L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ ι) n y) :
    ∃ s : SchemeHomOver ι f, L.IsTorsionPoint ι n s ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1 = y.1 := by sorry
