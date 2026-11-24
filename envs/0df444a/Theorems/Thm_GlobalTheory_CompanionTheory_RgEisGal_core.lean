-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_core
-- name    : GlobalTheory.CompanionTheory.RgEisGal.core
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:58:30.719091+00:00
-- url     : https://prove2.me/theorems/2461ad11-2dd4-459e-a6bf-0eb0de3eef8a
-- title:
--   Rg Eis Gal: core
-- statement:
--   The Rg Eis Gal construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L226-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L226-L368

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {T : Type} [TopologicalSpace T] [FirstCountableTopology T]
  {ES EA EB W : Type} [NormedAddCommGroup ES] [NormedSpace ℂ ES] [NormedAddCommGroup EA]
  [NormedSpace ℂ EA] [NormedAddCommGroup EB] [NormedSpace ℂ EB] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]

theorem GlobalTheory.CompanionTheory.RgEisGal.core (hId : IdTube) (hTC : TubeChain) (N R : ℝ) (hR : |N| + 1 ≤ R)
    {o₀ : ℂ × ℂ → T → ES →L[ℂ] W} {oc oa : ℂ × ℂ → T → EB →L[ℂ] W} {ob ol : ℂ × ℂ → T → EA →L[ℂ] W}
    (g₀ : TubeGood o₀ (coneI (10 * R))) (gc : TubeGood oc (coneC (10 * R)))
    (ga : TubeGood oa (coneA (10 * R))) (gb : TubeGood ob (coneC (10 * R)))
    (gl : TubeGood ol (coneI (10 * R)))
    {Dc Da Db d : ℂ → ℂ} (hDc : StripEntire Dc) (hDa : StripEntire Da) (hDb : StripEntire Db)
    (hd : StripEntire d)
    {Op₀ O : ℂ → ES →L[ℂ] EB} {Opc : ℂ → EB →L[ℂ] EB} {Opa : ℂ → EB →L[ℂ] EA} {Opb : ℂ → EA →L[ℂ] EA}
    (hOp₀ : LeftGood Op₀ (-R)) (hO : LeftGood O (1 / 2)) (hOpc : LeftGood Opc (-R))
    (hOpa : LeftGood Opa (-R)) (hOpb : LeftGood Opb (-R))
    (J₀ : ∀ l ∈ tube (chamberPairOneTwo (100 * R)), ∀ g, Dc (yv N l) • o₀ l g = (oc (mc N l) g).comp (Op₀ l.1))
    (J₁ : ∀ l ∈ tube (chamberPairTwoThree (100 * R)), ∀ g,
      Da (zv N l) • oc (mc N l) g = (oa (ma N l) g).comp (Opc (yv N l)))
    (J₂ : ∀ l ∈ tube (chamberPairThreeFour (100 * R)), ∀ g,
      Db l.2 • oa (ma N l) g = (ob (mb N l) g).comp (Opa (zv N l)))
    (J₃ : ∀ l ∈ tube (chamberPairFourLast (100 * R)), ∀ g,
      (-d (nz N l)) • (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1))) =
        (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1))))) :
    ∃ Φ : ℂ × ℂ → T → ES →L[ℂ] W, TubeGood Φ Set.univ ∧
      (∀ l ∈ tube (coneI (10 * R)), ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
        (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g) ∧
      ∀ l ∈ tube (Om4 N (10 * R)), ∀ g, (-d (nz N l)) • Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
        (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1)))) := by sorry
