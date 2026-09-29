-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_flat_etale_schemeKerStr_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFinite_flat_etale_schemeKerStr_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/fab36bd1-87f7-58e9-967b-81db16a61e00
-- title:
--   Kernel of [n] is finite flat étale when n∈ R^×
-- statement:
--   Let $R$ be a Noetherian local commutative ring and let $f : A \to \operatorname{Spec} R$ be a morphism of schemes equipped with a relative group law $L$: that is, functorially in a scheme $T$ over $\operatorname{Spec} R$ via $t : T \to \operatorname{Spec} R$, a group structure (multiplication, unit, inverse, with associativity, unit laws, left inverse, and compatibility of multiplication with base change along $\psi : T' \to T$ with $\psi \circ t = t'$) on the set of morphisms $T \to A$ over $t$. Assume $f$ satisfies `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} R$ is connected, and $f$ admits some relative group law; assume $L$ is commutative, i.e. its multiplication on $T$-points is commutative for every $t$; assume $f$ is smooth of some relative dimension $d$; and let $n$ be a natural number whose image in $R$ is a unit. Write $[n] : A \to A$ for the first component of the $n$-fold iterate of $L$-multiplication applied to the identity point of $A$, and form the pullback of $[n]$ against the unit section $\operatorname{Spec} R \to A$ of $L$. Then the second projection of this pullback, the structure morphism of the kernel $A[n] \to \operatorname{Spec} R$, is finite, flat and étale, and the first projection $A[n] \to A$ is a closed immersion.
--
--   This is the standard statement that, on a smooth commutative group scheme with connected proper fibres over a local Noetherian base, the $n$-torsion subscheme is a finite flat étale closed subscheme as soon as $n$ is invertible on the base. It supplies the finite étale torsion schemes used later for the Galois-module and eigenspace decompositions of torsion in the good-reduction Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_flat_etale_schemeKerStr_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_flat_etale_schemeKerStr_of_isUnit
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hA : AbelianSchemePropertyBundle R f) (hcomm : L.IsCommutative)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ) (hn : IsUnit (n : R)) :
    IsFinite (L.schemeKerStr n) ∧ Flat (L.schemeKerStr n) ∧ Etale (L.schemeKerStr n) ∧
    IsClosedImmersion (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) := by sorry
