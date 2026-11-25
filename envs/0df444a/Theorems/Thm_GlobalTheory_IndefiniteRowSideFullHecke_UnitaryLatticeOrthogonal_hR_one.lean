-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryLatticeOrthogonal_hR_one
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.hR_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:20.285827+00:00
-- url     : https://prove2.me/theorems/70bcbb1a-2a8c-43c7-8095-e68c3f16d4e1
-- title:
--   Unitary Lattice Orthogonal: h R one
-- statement:
--   The Unitary Lattice Orthogonal construction uses the h R one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/UnitaryLatticeOrthogonal.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/UnitaryLatticeOrthogonal.lean#L159-L163

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.hR_one {M : ℕ} (z y : Fin M → Ev F E v) :
    hR (Fv F v) σ (1 : Matrix (Fin M) (Fin M) E) z y = ∑ i, sigR (Fv F v) σ (z i) * y i := by sorry
