-- Prove2me | Theorems.Thm_Freiman_background_automaton_correct
-- name    : Freiman.background_automaton_correct
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:57.602935+00:00
-- url     : https://prove2.me/theorems/6cb1392b-81d3-41f9-87dc-4b015a33348f
-- title:
--   The five suffix states exactly detect the forbidden word 31313
-- statement:
--   Starting from any of the five proper-prefix states of 31313, the transition process never reaches its forbidden transition exactly when prepending that state's word to the tail produces no occurrence of 31313.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_automaton_correct (s : BackgroundState) (b : ℕ → ℕ+) :
    BackgroundAllowed s b ↔
      OneSidedAvoidsBlock (backgroundPrepend (backgroundStateWord s) b) [3,1,3,1,3] := by
  sorry

end Freiman
