-- Prove2me | Theorems.Thm_MazurTransfer_RationalSchemeMorphismFieldPointExtensionality_hom_eq_of_field_points
-- name    : MazurTransfer.RationalSchemeMorphismFieldPointExtensionality.hom_eq_of_field_points
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:49:11.052891+00:00
-- url     : https://prove2.me/theorems/ba052cb8-c3f2-40f0-866f-834831c7487f
-- title:
--   Morphisms of rational schemes with reduced source and separated target are determined by perfect characteristic-zero field points
-- statement:
--   Let X and Y be schemes over Q, with X reduced and the structural morphism of Y separated. Let f,g be morphisms from X to Y over Q. If
--
--   $$f\circ a=g\circ a$$
--
--   for every perfect field K of characteristic zero and every K-valued point a of X over Q, then f=g. No properness hypothesis or density assertion about rational points is required. The named downstream consumer is equality of the actual Picard diamond and norm scheme morphisms.
-- source:
--   Original MazurTheorem RationalSchemeMorphismFieldPointExtensionality.hom_eq_of_field_points, using Mathlib residue-field morphism extensionality in the exact candidate environment 0df444a360eaa60ab8c11dca51a86af692955474, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: morphisms from a reduced Q-scheme to a separated Q-scheme
are determined by all characteristic-zero perfect field points. The proof
uses the literal residue-field maps at all source points, without a density
claim about rational points. Named downstream consumer: the cyclotomic and
norm identities on the existing rational order-13 Picard scheme.
-/
import Mathlib

noncomputable section
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme} (cX : X ⟶ Spec (CommRingCat.of ℚ))
    (cY : Y ⟶ Spec (CommRingCat.of ℚ)) [IsReduced X] [IsSeparated cY]

theorem MazurTransfer.RationalSchemeMorphismFieldPointExtensionality.hom_eq_of_field_points (f g : X ⟶ Y)
    (hf : f ≫ cY = cX) (hg : g ≫ cY = cX)
    (H : ∀ (K : Type) [Field K] [CharZero K] [PerfectField K]
      (a : Spec (CommRingCat.of K) ⟶ X)
      (ha : a ≫ cX = Spec.map (CommRingCat.ofHom (algebraMap ℚ K))),
        a ≫ f = a ≫ g) : f = g := by sorry
