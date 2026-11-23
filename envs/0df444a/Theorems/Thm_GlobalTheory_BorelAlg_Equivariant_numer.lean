-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_Equivariant_numer
-- name    : GlobalTheory.BorelAlg.Equivariant.numer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:26.746212+00:00
-- url     : https://prove2.me/theorems/cff0b8ad-5e46-4778-ac35-7ce204a68f3a
-- title:
--   Equivariant: numer
-- statement:
--   The Equivariant construction uses the numer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L106-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L106-L136

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
variable [Fintype ι]
variable {m L} {S : Type} [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
  [IsLocalization.Away (∏ τ, (gen m L τ).det) S]

theorem GlobalTheory.BorelAlg.Equivariant.numer {a : ι × ℕ → ℕ} {f : S} (hf : Equivariant m L S a f)
    {P : MvPolynomial (Lt m) L} {N : ℕ}
    (hP : f * algebraMap _ S ((∏ τ, (gen m L τ).det) ^ N) = algebraMap _ S P)
    {T : Type} [Field T] (c : L →+* T) (x y b : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T)
    (hx : ∀ τ, (x τ).det ≠ 0) (hy : ∀ τ, (y τ).det ≠ 0) (hb : ∀ τ i j, i < j → b τ i j = 0)
    (hxy : ∀ τ, y τ = b τ * x τ) :
    eval₂Hom c (fun p : Lt m => y p.1 p.2.1 p.2.2) P * (∏ τ, (x τ).det) ^ N =
      (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) *
        eval₂Hom c (fun p : Lt m => x p.1 p.2.1 p.2.2) P * (∏ τ, (y τ).det) ^ N := by sorry
