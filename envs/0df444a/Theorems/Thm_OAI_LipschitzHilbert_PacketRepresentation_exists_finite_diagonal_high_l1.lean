-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_exists_finite_diagonal_high_l1
-- name    : OAI.LipschitzHilbert.PacketRepresentation.exists_finite_diagonal_high_l1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:48:57.345982+00:00
-- url     : https://prove2.me/theorems/5bb50156-6cd6-478d-8cbe-25c67b14dd0a
-- title:
--   OAI.LipschitzHilbert.PacketRepresentation.exists_finite_diagonal_high_l1: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketRepresentation.exists_finite_diagonal_high_l1` of [lean/OAI/Analysis/LipschitzHilbert/Phase/FiniteDiagonalHighL1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/FiniteDiagonalHighL1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketRepresentation`, with `open Set MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem exists_finite_diagonal_high_l1 (hVariation : LepingleInput) (hLL : LaceyLiInput)
--       (psi beta : SchwartzMap ℝ ℂ) (A B c C a M delta F c0 : ℝ)
--       (p : AnnularPacketGeometry A B c C a M) (hA : 0<A) (hB : 0<B)
--       (hd : 0<delta) (hnarrow : delta*C≤A/2) (hF : 0≤F) (hc0 : 0 < c0)
--       (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
--       (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
--       ∃ K L0 : ℝ, 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
--       ∀ (N : ℕ) (κ : Type) [Fintype κ]
--         (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
--         topLength≤Real.exp (-(L^(97/100:ℝ))) →
--         (∀ j : Fin N, (p.H+M/c+delta)*(w/(topLength/(2:ℝ)^j.val))≤3/4) →
--       ∀ (center : κ → ℝ), (∀ k, c0/w≤|2*Real.pi*center k|) →
--         (∀ k, |2*Real.pi*center k|≤F/w) →
--         (∀ k, c+B*(w/width)≤w*center k) →
--         (∀ k, w*center k+B*(w/width)≤C) →
--       ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
--       ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
--         (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
--         (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
--       ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
--         planeMeasure E≠∞ → planeMeasure Fset≠∞ → 0<planeMeasure.real Fset →
--         (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
--       ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
--         (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
--         0 < ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
--         planeMeasure.real E=ratio^2*planeMeasure.real Fset →
--         Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
--         width=widthScale*w →
--         ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
--           (fun z => field (planeCoordinates z)) f g‖≤
--           K*L^(-20:ℝ)*Real.sqrt (planeMeasure.real Fset)*Real.sqrt (planeMeasure.real E)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LaceyLiInput`, `OAI.LipschitzHilbert.LepingleInput` and `OAI.LipschitzHilbert.PacketRepresentation.planeMeasure` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.planeCoordinates` and `OAI.LipschitzHilbert.PacketRepresentation.AnnularPacketGeometry` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.PacketRepresentation.finiteDiagonalBandL1` (definitions bundle `OAIQ090A002` of this split); `OAI.LipschitzHilbert.Plane` (the published bundle `Def_LipschitzHilbert`).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketRepresentation.band_projected_high` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/FiniteDiagonalHighL1.lean (declaration OAI.LipschitzHilbert.PacketRepresentation.exists_finite_diagonal_high_l1)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_finite_diagonal_high_l1 (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi beta : SchwartzMap ℝ ℂ) (A B c C a M delta F c0 : ℝ)
    (p : AnnularPacketGeometry A B c C a M) (hA : 0<A) (hB : 0<B)
    (hd : 0<delta) (hnarrow : delta*C≤A/2) (hF : 0≤F) (hc0 : 0 < c0)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K L0 : ℝ, 0<K ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (topLength width w : ℝ), 0<topLength → 0<width → 0<w → w≤width →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, (p.H+M/c+delta)*(w/(topLength/(2:ℝ)^j.val))≤3/4) →
    ∀ (center : κ → ℝ), (∀ k, c0/w≤|2*Real.pi*center k|) →
      (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, c+B*(w/width)≤w*center k) →
      (∀ k, w*center k+B*(w/width)≤C) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f : κ → (ℝ×ℝ) → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      planeMeasure E≠∞ → planeMeasure Fset≠∞ → 0<planeMeasure.real Fset →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
    ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
      0 < ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
      planeMeasure.real E=ratio^2*planeMeasure.real Fset →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      width=widthScale*w →
      ‖finiteDiagonalBandL1 (N:=N) psi beta topLength width center
        (fun z => field (planeCoordinates z)) f g‖≤
        K*L^(-20:ℝ)*Real.sqrt (planeMeasure.real Fset)*Real.sqrt (planeMeasure.real E) := by
  sorry

end LipschitzHilbert.PacketRepresentation

end

end OAI
end
