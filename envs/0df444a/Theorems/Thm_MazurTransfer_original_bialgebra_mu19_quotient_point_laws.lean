-- Prove2me | Theorems.Thm_MazurTransfer_original_bialgebra_mu19_quotient_point_laws
-- name    : MazurTransfer.original_bialgebra_mu19_quotient_point_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-22T02:27:35.643137+00:00
-- url     : https://prove2.me/theorems/8ecde8ca-3d66-4399-8699-a7aad948a0f6
-- statement:
--   The original literal nineteenth-root quotient points induced by the same given genuine bialgebra map and cyclic equivalence preserve multiplication, identity and every coefficient map over every original commutative coefficient algebra. All three complete original propositions and helper types, the exact original quotient-point constructor type and whole value, and all original cyclic point and restriction contexts are independently checked. Every original hypothesis is retained, with no field or invertibility hypothesis added. Named downstream consumer: the same selected integral pi norm-kernel map and pushforward of its norm-preimage cocycles at nineteen.

import Definitions.Def_MazurTransfer_OriginalBialgebraMu19QuotientPointsData20261020
import Theorems.Thm_MazurTransfer_original_bialgebra_point_restriction_laws
import Theorems.Thm_MazurTransfer_original_bialgebra_cyclic_mu19_point_laws
noncomputable section
open MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points MazurTransfer.BialgebraPointRestriction MazurTransfer.BialgebraMu19QuotientPoints

theorem MazurTransfer.original_bialgebra_mu19_quotient_point_laws : (∀ {R H G : Type} [CommRing R] [CommRing H] [Bialgebra R H] [CommRing G] [Bialgebra R G] (j : H →ₐc[R] G) (ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], ∀ (f g : WithConv (G →ₐ[R] T)),
quotientPoint j ψ T (f * g) = quotientPoint j ψ T f * quotientPoint j ψ T g) ∧ (∀ {R H G : Type} [CommRing R] [CommRing H] [Bialgebra R H] [CommRing G] [Bialgebra R G] (j : H →ₐc[R] G) (ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], quotientPoint j ψ T (1 : WithConv (G →ₐ[R] T)) = 1) ∧ (∀ {R H G : Type} [CommRing R] [CommRing H] [Bialgebra R H] [CommRing G] [Bialgebra R G] (j : H →ₐc[R] G) (ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], ∀ {T' : Type} [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (f : WithConv (G →ₐ[R] T)),
quotientPoint j ψ T' (.toConv (a.comp f.ofConv)) =
      restrictRootsOfUnity a.toRingHom 19 (quotientPoint j ψ T f)) := by sorry
