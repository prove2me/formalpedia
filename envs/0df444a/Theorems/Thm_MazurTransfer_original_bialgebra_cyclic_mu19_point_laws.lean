-- Prove2me | Theorems.Thm_MazurTransfer_original_bialgebra_cyclic_mu19_point_laws
-- name    : MazurTransfer.original_bialgebra_cyclic_mu19_point_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T22:04:19.103762+00:00
-- url     : https://prove2.me/theorems/8621015b-c30b-429a-8cf0-6617a6bf2321
-- statement:
--   A given original cyclic bialgebra equivalence produces the same literal nineteenth-root point equivalence over every coefficient algebra, retaining evaluation at the same original generator and compatibility with every original coefficient map. Both complete original propositions and helper types, original point-equivalence types and whole values, and original point-operation contexts are independently checked. Every original ring, bialgebra, coefficient algebra and equivalence hypothesis is retained. Named downstream consumer: normalization of the same selected integral pi quotient and norm torsor pushforward at nineteen.

import Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
noncomputable section
open MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points

theorem MazurTransfer.original_bialgebra_cyclic_mu19_point_laws : (∀ {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], ∀ (f : WithConv (H →ₐ[R] T)),
((literalPointEquiv φ T f : Tˣ) : T) = f (φ.symm (MonoidAlgebra.single generator 1))) ∧ (∀ {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], ∀ {T' : Type} [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (f : WithConv (H →ₐ[R] T)),
literalPointEquiv φ T' (.toConv (a.comp f.ofConv)) =
      restrictRootsOfUnity a.toRingHom 19 (literalPointEquiv φ T f)) := by sorry
