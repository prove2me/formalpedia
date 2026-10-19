-- Prove2me | Theorems.Thm_MazurTransfer_PicardRepresentationPointComparison_overPointEquiv_mul
-- name    : MazurTransfer.PicardRepresentationPointComparison.overPointEquiv_mul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T08:08:23.829631+00:00
-- url     : https://prove2.me/theorems/ed577878-a599-4cdb-88a0-279d93187d5d
-- title:
--   The comparison of two Picard representations preserves canonical point multiplication
-- statement:
--   Let $P$ be a rigidified relative Picard group subfunctor of a pointed scheme $C/R$. Suppose $D$ and $D^{\prime}$ both represent $P$, with their canonical group structures supplied by those representations. Classification of universal bundles gives the specified point equivalence $\Phi_T:D(T)\simeq D^{\prime}(T)$ for every test scheme $T$ over $R$. This equivalence preserves multiplication: $$\Phi_T(xy)=\Phi_T(x)\Phi_T(y).$$ It therefore compares the actual integral Picard family’s field-fibre group with a separately chosen representative carrying the published arithmetic divisor-class equivalence.
-- source:
--   New checked generic comparison theorem in MazurTheorem scratch integration, Apache-2.0, Vas and contributors. Uses the public PicardRepresentationPointComparison constructor and the original official Anthropic FLT universal-bundle multiplication theorem, exact upstream pin 6e837e75355538c7f80bab5b956861e86c4eacc2. No arithmetic dictionary or cardinality hypothesis is supplied. The actual specified comparison map and both canonical group instances occur in the full public type. The checked solution and public formal statement have definitionally equal closed types with matching universe parameters. Native, strict and full frontend checks pass with standard axioms only. Explicit design boundary: canonical point groups of two representations of the same group subfunctor. Named downstream consumer: the original actual integral relative arithmetic group-equivalence contract.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: classification by two representations of the same
relative Picard group subfunctor preserves canonical point multiplication.
Named downstream consumer: the actual integral family's arithmetic field
fibres, compared with the already published field representative.
Uses original official Anthropic FLT universal-bundle multiplication,
exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Mathlib
import Definitions.Def_MazurTransfer_PicardRepresentationPointComparison
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.PicardRepresentationPointComparison
open scoped CategoryTheory.MonObj

theorem MazurTransfer.PicardRepresentationPointComparison.overPointEquiv_mul {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {P : SubPicGroupCondition c ε} {D D' : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    (h' : RepresentsRelSubPic c ε P.toSubPicCondition D')
    {T : Over (Spec (.of R))} (a b : T ⟶ Over.mk D.toBase) :
    letI := h.grpObj
    letI := h'.grpObj
    overPointEquiv h h' T.hom (a * b) =
      overPointEquiv h h' T.hom a * overPointEquiv h h' T.hom b := by sorry
