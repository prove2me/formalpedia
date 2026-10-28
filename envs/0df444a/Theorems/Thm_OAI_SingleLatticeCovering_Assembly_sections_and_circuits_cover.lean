-- Prove2me | Theorems.Thm_OAI_SingleLatticeCovering_Assembly_sections_and_circuits_cover
-- name    : OAI.SingleLatticeCovering.Assembly.sections_and_circuits_cover
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T12:53:31.679559+00:00
-- url     : https://prove2.me/theorems/df78bfa7-7a96-4c76-ac4c-f5b1a7dd5faa
-- title:
--   OAI.SingleLatticeCovering.Assembly.sections_and_circuits_cover: intermediate lemma from OpenAI, A single-lattice covering bound of order n log n
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SingleLatticeCovering.single_lattice_covering`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A single-lattice covering bound of order n log n*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SingleLatticeCovering.Assembly.sections_and_circuits_cover` of [lean/OAI/Geometry/LatticeCovering/MeanHoles.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/MeanHoles.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SingleLatticeCovering.Assembly`, with `open MeasureTheory Filter Set`, `open scoped Topology`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open Module Submodule MeasureTheory`, `open scoped BigOperators`, `open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal`, `open scoped BigOperators Pointwise ENNReal`):
--
--   ```lean
--   theorem sections_and_circuits_cover {B : Block} (c : Chain B) {m : ℕ}
--       (hm : 270 ≤ m) (hD : 0 < c.fullDim)
--       (K : Set (Fin (m+c.fullDim) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
--       (hV : 0 < (volume K).toReal) {R : ℝ} (hR : 0 < R)
--       (hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2)
--       (hsmall : R^2/(m : ℝ)^2 ≤ 1)
--       (hgauss : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
--         (volume K).toReal*gamma y/2 ≤ (volume (coordinateFiber K y)).toReal)
--       (κ ρ ε τ A : ℝ) (hρ : 0 < ρ) (hτ : 0 ≤ τ) (hA : 0 < A)
--       (hpat : ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
--         P.Nonempty ∧ SuffixBinary P ∧
--         (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧ c.det*gamma (y-c.fullLinear l) ≤ ε) ∧
--         κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l))
--       (hload : A+(2^c.fullDim : ℕ)*τ ≤ (Real.exp (-1)/8)*κ*ρ)
--       (hcap : (Real.exp 1/8)*ρ*ε ≤ FinalRates.eta m)
--       (hcriterion : 302*(3*(m : ℝ)^2)^c.fullDim*Real.exp (-τ/2)<1)
--       (hcount : ∀ {α : Type} (s : Finset α), (s.card : ℝ) ≤ (3*(m : ℝ)^2)^c.fullDim →
--         let Lstar := 2*((patternTotal c.alphabetSeq s c.fullDim : ℝ)+1)
--         1 ≤ Lstar ∧ (patternTotal c.alphabetSeq s c.fullDim : ℝ)<Lstar ∧
--         Real.exp ((2 : ℝ)^c.fullDim*Real.log Lstar-A/2) ≤
--           1/((m+c.fullDim : ℕ) : ℝ)^(2*(m+c.fullDim))) :
--       ∃ (Λ : Submodule ℤ (Fin (m+c.fullDim) → ℝ)) (_ : DiscreteTopology Λ),
--         IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+c.fullDim) → ℝ))=Set.univ ∧
--         (volume K).toReal/ZLattice.covolume Λ volume ≤ Real.exp 1*ρ
--   ```
--
--   **Definitions.** The statement is written with `OAI.SingleLatticeCovering.FinalRates.eta`, `OAI.SingleLatticeCovering.Folded.gamma`, `OAI.SingleLatticeCovering.Sections.coordinateFiber`, `OAI.SingleLatticeCovering.Shear.patternTotal`, `OAI.SingleLatticeCovering.Vertical.Block`, `OAI.SingleLatticeCovering.Vertical.Chain`, `OAI.SingleLatticeCovering.Vertical.SuffixBinary`, `OAI.SingleLatticeCovering.Vertical.Block.terminalDim`, `OAI.SingleLatticeCovering.Vertical.Chain.FullResidual`, `OAI.SingleLatticeCovering.Vertical.Chain.FullVec`, `OAI.SingleLatticeCovering.Vertical.Chain.alphabetSeq`, `OAI.SingleLatticeCovering.Vertical.Chain.det`, `OAI.SingleLatticeCovering.Vertical.Chain.fullDim`, `OAI.SingleLatticeCovering.Vertical.Chain.fullLinear`, `OAI.SingleLatticeCovering.Vertical.Chain.fullRaw` and `OAI.SingleLatticeCovering.Vertical.Chain.radiusSq` (definitions bundle `OAIB3Sl000` of this split).
--
--   **Used by.** The proof of `OAI.SingleLatticeCovering.single_lattice_covering` of this split imports it.
-- source:
--   OpenAI, A single-lattice covering bound of order n log n, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-single-lattice-covering-bound-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/MeanHoles.lean (declaration OAI.SingleLatticeCovering.Assembly.sections_and_circuits_cover)

import Mathlib
import Definitions.Def_OAIB3Sl000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section

noncomputable section
namespace SingleLatticeCovering.Assembly
open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal
open scoped BigOperators Pointwise ENNReal

theorem sections_and_circuits_cover {B : Block} (c : Chain B) {m : ℕ}
    (hm : 270 ≤ m) (hD : 0 < c.fullDim)
    (K : Set (Fin (m+c.fullDim) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) {R : ℝ} (hR : 0 < R)
    (hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2)
    (hsmall : R^2/(m : ℝ)^2 ≤ 1)
    (hgauss : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
      (volume K).toReal*gamma y/2 ≤ (volume (coordinateFiber K y)).toReal)
    (κ ρ ε τ A : ℝ) (hρ : 0 < ρ) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hpat : ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
      P.Nonempty ∧ SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧ c.det*gamma (y-c.fullLinear l) ≤ ε) ∧
      κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l))
    (hload : A+(2^c.fullDim : ℕ)*τ ≤ (Real.exp (-1)/8)*κ*ρ)
    (hcap : (Real.exp 1/8)*ρ*ε ≤ FinalRates.eta m)
    (hcriterion : 302*(3*(m : ℝ)^2)^c.fullDim*Real.exp (-τ/2)<1)
    (hcount : ∀ {α : Type} (s : Finset α), (s.card : ℝ) ≤ (3*(m : ℝ)^2)^c.fullDim →
      let Lstar := 2*((patternTotal c.alphabetSeq s c.fullDim : ℝ)+1)
      1 ≤ Lstar ∧ (patternTotal c.alphabetSeq s c.fullDim : ℝ)<Lstar ∧
      Real.exp ((2 : ℝ)^c.fullDim*Real.log Lstar-A/2) ≤
        1/((m+c.fullDim : ℕ) : ℝ)^(2*(m+c.fullDim))) :
    ∃ (Λ : Submodule ℤ (Fin (m+c.fullDim) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+c.fullDim) → ℝ))=Set.univ ∧
      (volume K).toReal/ZLattice.covolume Λ volume ≤ Real.exp 1*ρ := by
  sorry

end SingleLatticeCovering.Assembly

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end
