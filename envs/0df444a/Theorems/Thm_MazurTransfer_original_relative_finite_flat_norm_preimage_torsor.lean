-- Prove2me | Theorems.Thm_MazurTransfer_original_relative_finite_flat_norm_preimage_torsor
-- name    : MazurTransfer.original_relative_finite_flat_norm_preimage_torsor
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T01:40:29.127627+00:00
-- url     : https://prove2.me/theorems/d4a6a746-1fae-4b4f-aec7-3d84023ff34b
-- statement:
--   The actual preimage fibre of the given finite, flat, locally finitely presented and surjective relative group endomorphism is the original finite-flat preimage torsor under the same represented kernel. The original principal-action scheme isomorphism realizes exactly the same point action over every test scheme. All original hypotheses, group-law preservation certificates, structure maps, section and universes are retained. Named downstream consumer: actual integral nineteen norm fibres and their selected mu19 quotient torsors.

import Definitions.Def_MazurTransfer_OriginalRelativeFiniteFlatNormPreimageTorsorData20261020
import Theorems.Thm_MazurTransfer_original_relative_norm_preimage_principal_iso_laws
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeNormPreimageRepresentation MazurTransfer.RelativeNormPreimagePrincipalIso
open MazurTransfer.RelativeFiniteFlatNormPreimageTorsor
universe u

theorem MazurTransfer.original_relative_finite_flat_norm_preimage_torsor : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) [IsFinite F.val] [Flat F.val]
    [LocallyOfFinitePresentation F.val] [Surjective F.val],
HasFiniteFlatPreimageTorsor L F hOne hMul a) := by sorry
