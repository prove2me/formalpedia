-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_of_charts
-- name    : GlobalTheory.AffineQuotient.of_charts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:01.849852+00:00
-- url     : https://prove2.me/theorems/a2da169a-e54a-4115-8031-d47bd42f2acf
-- title:
--   Affine Quotient: of charts
-- statement:
--   The Affine Quotient construction uses the of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L212-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L212-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency false
omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]

theorem GlobalTheory.AffineQuotient.of_charts (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P] {ι : Type}
    (X' Y' : ι → Scheme.{0}) (u : ∀ i, X' i ⟶ X) (v : ∀ i, Y' i ⟶ Y) (f' : ∀ i, X' i ⟶ Y' i)
    [∀ i, IsOpenImmersion (v i)] (hv : ∀ y, ∃ i z, v i z = y)
    (h : ∀ i, IsPullback (f' i) (u i) (v i) f) (hP : ∀ i, P (f' i)) : P f := by sorry
