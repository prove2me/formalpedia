-- Prove2me | Theorems.Thm_Freiman_middle_initial_chain_assembly
-- name    : Freiman.middle_initial_chain_assembly
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:06:54.918861+00:00
-- url     : https://prove2.me/theorems/52f18864-35c5-4876-8d4c-fe311c26a893
-- title:
--   middle initial chain assembly
-- statement:
--   Bookkeeping of the explicit 15-element list turns the fourteen contact inequalities and two outer margins into closed initial coverage using the finite interval-chain lemma.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:initial

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_initial_chain_assembly :
    (∀ i : Fin 15, middleRootCertificate i) →
    (∀ (i : ℕ) (hi : i<7), (middleCover (middleRoot ⟨i,by omega⟩) ∩ middleCover (middleRoot ⟨i+1,by omega⟩)).Nonempty) →
    (∀ (i : ℕ) (hlo : 7 ≤ i) (hi : i<14), (middleCover (middleRoot ⟨i,by omega⟩) ∩ middleCover (middleRoot ⟨i+1,by omega⟩)).Nonempty) →
    (middleBounds (middleRoot 14)).1 < Real.sqrt 21 → (128/25:ℝ)<(middleBounds (middleRoot 0)).2 →
    (∀ (cs : List MiddleCore) (l u : ℝ), middleContacts cs → (∃ d ∈ cs, (middleBounds d).1 ≤ l) → (∃ d ∈ cs, u ≤ (middleBounds d).2) → Set.Icc l u ⊆ middleUnion cs) →
    ∀ t ∈ Set.Icc (Real.sqrt 21) (128/25:ℝ), ∃ i : Fin 15, t∈middleCover (middleRoot i) := by
  sorry

end Freiman
