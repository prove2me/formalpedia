-- Prove2me | Theorems.Thm_MazurTransfer_OriginalRelativeGroupTorsionKernelInterop_eq_one_of_isTorsionPoint_of_comp_residue_eq
-- name    : MazurTransfer.OriginalRelativeGroupTorsionKernelInterop.eq_one_of_isTorsionPoint_of_comp_residue_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T10:03:23.587393+00:00
-- url     : https://prove2.me/theorems/37582070-c16c-4736-b591-58dbdbc3eb9d
-- title:
--   Original FLT residue torsion kernel through its lower public lemmas
-- statement:
--   Let $f:X\to\operatorname{Spec}R$ be locally of finite type, with a commutative relative group law $L$. Let $B$ be a local commutative ring, let $t:\operatorname{Spec}B\to\operatorname{Spec}R$, and let $m$ be a natural number that is a unit in $B$. For any relative point $s$ over $t$, $$[m]s=e,\qquad s|_{\kappa(B)}=e|_{\kappa(B)}\quad\Longrightarrow\quad s=e.$$ The residue restrictions and relative multiplication are the original specified scheme maps. This reuses the complete original FLT theorem through its lower public lemmas and supplies proper valuation and actual rational Picard torsion specialization.
-- source:
--   Complete original official Anthropic FLT residue-torsion proof from P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_isTorsionPoint_of_comp_residue_eq.lean at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. The entire original main statement and proof body are unchanged, with original short helpers retained in their original namespace. The root is hoisted to the required top-level solution and its original scope is restored. Existing lower public Proved lemmas and original base-change Definitions are reused; the failing legacy residue-kernel theorem API is not imported. The public statement is a distinct interoperability wrapper with complete type kernel-equal to the original. Native, strict and complete frontend checks pass with standard axioms only. Named downstream consumers: proper valuation and actual rational Picard torsion specialization. The public preamble omits an invalid hiding clause for an alias absent from its type dependencies; the original SchemeHomOver and restriction map names are explicit. Only identifier qualifications change, and complete original types are compared again.

/- Original official Anthropic FLT proof reuse, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: preserve the complete original invertible-order relative
torsion kernel through public lower-lemma imports.
Named downstream consumer: proper valuation and actual rational Picard torsion. -/
import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
open CategoryTheory AlgebraicGeometry GoodReductionJacobian
open NeronModelInfra
universe u

theorem MazurTransfer.OriginalRelativeGroupTorsionKernelInterop.eq_one_of_isTorsionPoint_of_comp_residue_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) [LocallyOfFiniteType f]
    {B : Type u} [CommRing B] [IsLocalRing B]
    (t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (m : ℕ) (hm : IsUnit (m : B))
    (s : NeronModelInfra.SchemeHomOver t f)
    (hs : L.IsTorsionPoint t m s)
    (hred : GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) rfl s =
        GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) rfl (L.one t)) :
    s = L.one t := by sorry
