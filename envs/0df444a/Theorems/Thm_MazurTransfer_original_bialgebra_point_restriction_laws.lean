-- Prove2me | Theorems.Thm_MazurTransfer_original_bialgebra_point_restriction_laws
-- name    : MazurTransfer.original_bialgebra_point_restriction_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T01:53:13.756978+00:00
-- url     : https://prove2.me/theorems/1b28f5f0-0d0f-48f1-98a0-e93be14370aa
-- statement:
--   The original bialgebra inclusion induces the same arithmetic point restriction over every original coefficient algebra. It preserves convolution multiplication and identity, and commutes with every original coefficient map. All original bialgebras, inclusion, algebra structures and universes are retained. Named downstream consumer: actual integral norm-kernel character quotients and their torsor cocycles.

import Definitions.Def_MazurTransfer_OriginalBialgebraPointRestrictionData20261020
noncomputable section

open MazurTransfer.BialgebraPointRestriction
universe u

theorem MazurTransfer.original_bialgebra_point_restriction_laws : (∀ {R H G : Type u} [CommRing R] [CommRing H] [CommRing G] [Bialgebra R H] [Bialgebra R G] (ι : H →ₐc[R] G), ∀ {T : Type u} [CommRing T] [Algebra R T]
    (f g : WithConv (G →ₐ[R] T)),
restrictPoint ι (f * g) = restrictPoint ι f * restrictPoint ι g) ∧ (∀ {R H G : Type u} [CommRing R] [CommRing H] [CommRing G] [Bialgebra R H] [Bialgebra R G] (ι : H →ₐc[R] G), ∀ {T : Type u} [CommRing T] [Algebra R T],
restrictPoint ι (1 : WithConv (G →ₐ[R] T)) = 1) ∧ (∀ {R H G : Type u} [CommRing R] [CommRing H] [CommRing G] [Bialgebra R H] [Bialgebra R G] (ι : H →ₐc[R] G), ∀ {T T' : Type u} [CommRing T] [Algebra R T]
    [CommRing T'] [Algebra R T'] (g : T →ₐ[R] T') (f : WithConv (G →ₐ[R] T)),
restrictPoint ι (.toConv (g.comp f.ofConv)) =
      WithConv.toConv (g.comp (restrictPoint ι f).ofConv)) := by sorry
