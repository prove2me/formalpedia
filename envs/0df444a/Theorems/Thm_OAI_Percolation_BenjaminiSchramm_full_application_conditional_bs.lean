-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_full_application_conditional_bs
-- name    : OAI.Percolation.BenjaminiSchramm.full_application_conditional_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:38:19.599684+00:00
-- url     : https://prove2.me/theorems/dd8c4fbb-339a-4c03-95f8-cc23f05303b7
-- title:
--   OAI.Percolation.BenjaminiSchramm.full_application_conditional_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.BenjaminiSchramm.full_application_conditional` of [lean/OAI/Probability/BenjaminiSchramm/Application.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/Application.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.BenjaminiSchramm`, with `open MeasureTheory`):
--
--   ```lean
--   theorem full_application_conditional_bs [Infinite V]
--       (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
--       (hqt : QuasiTransitive G) (hh : 0 < hV G)
--       (hutchcroft2019 :
--         ¬ AutUnimodular (subdivision G) (subdivision_injective G)
--           (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
--         pc (subdivision G) < ptwo (subdivision G))
--       (hfirst : HutchcroftFirstMomentInput (subdivision G))
--       (htheta : TrianglePercolationProbabilityInput (subdivision G))
--       (hvolume : HutchcroftCriticalVolumeInput (subdivision G))
--       (hradii : HutchcroftCriticalRadiiInput (subdivision G)) :
--       MainConclusion G ∧ CriticalLawsConclusion G
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.SubdivisionEdge` and `OAI.Percolation.subdivision` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.AutUnimodular`, `OAI.Percolation.subdivision_connected`, `OAI.Percolation.subdivision_injective`, `OAI.Percolation.subdivision_locallyFinite`, `OAI.Percolation.BenjaminiSchramm.HutchcroftCriticalRadiiInput`, `OAI.Percolation.BenjaminiSchramm.HutchcroftCriticalVolumeInput`, `OAI.Percolation.BenjaminiSchramm.HutchcroftFirstMomentInput` and `OAI.Percolation.BenjaminiSchramm.TrianglePercolationProbabilityInput` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.MainConclusion`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.hV`, `OAI.Percolation.pc`, `OAI.Percolation.ptwo` and `OAI.Percolation.BenjaminiSchramm.CriticalLawsConclusion` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.full_application_reduced_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/Application.lean (declaration OAI.Percolation.BenjaminiSchramm.full_application_conditional)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Percolation.BenjaminiSchramm

open MeasureTheory

universe u v
variable {V : Type u} {E : Type v}

theorem full_application_conditional_bs [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (hutchcroft2019 :
      ¬ AutUnimodular (subdivision G) (subdivision_injective G)
        (subdivision_connected G hconn) (subdivision_locallyFinite G hloc) →
      pc (subdivision G) < ptwo (subdivision G))
    (hfirst : HutchcroftFirstMomentInput (subdivision G))
    (htheta : TrianglePercolationProbabilityInput (subdivision G))
    (hvolume : HutchcroftCriticalVolumeInput (subdivision G))
    (hradii : HutchcroftCriticalRadiiInput (subdivision G)) :
    MainConclusion G ∧ CriticalLawsConclusion G := by
  sorry

end Percolation.BenjaminiSchramm

end OAI
end
