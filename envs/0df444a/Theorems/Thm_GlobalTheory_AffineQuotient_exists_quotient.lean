-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_exists_quotient
-- name    : GlobalTheory.AffineQuotient.exists_quotient
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:54:35.171344+00:00
-- url     : https://prove2.me/theorems/10e888d9-f8f5-44af-bafd-56e8574bb3eb
-- title:
--   Affine Quotient: exists quotient
-- statement:
--   The Affine Quotient construction uses the exists quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L299-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean#L299-L323

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

theorem GlobalTheory.AffineQuotient.exists_quotient [IsFinite f] [IsAffineHom g] [IsLocallyNoetherian Y]
    (H : ∀ U : Y.affineOpens, (invariants f g a ha p hp U.1).subtype.FaithfullyFlat ∧
      IsPushout (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype)
        (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype)
        (pullOver f g a ha U.1) (pullOver f g p hp U.1)) :
    ∃ (Q : Scheme.{0}) (q : X ⟶ Q) (π : Q ⟶ Y), q ≫ π = f ∧ IsFinite π ∧ IsFinite q ∧ Flat q ∧
      Surjective q ∧ IsPullback a p q q := by sorry
