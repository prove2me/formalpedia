-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_t_zx
-- name    : GlobalTheory.CompanionTheory.GapOpMain.t_zx
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:42:41.316489+00:00
-- url     : https://prove2.me/theorems/0e2af3b0-8660-44d2-bca5-7c3f3978fdf6
-- title:
--   Gap Op Main: t zx
-- statement:
--   The Gap Op Main construction uses the t zx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SumHyperplanesComplementFlags.lean#L240-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SumHyperplanesComplementFlags.lean#L240-L282

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}

theorem GlobalTheory.CompanionTheory.GapOpMain.t_zx (hD : LatData k n B red ρ t v) (j : ℕ) :
    t (zx v (e0 k n) j) = ∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => M ≤ H0 k n ∧ Module.finrank k M + (j + 1) = n + 1), v M := by sorry
