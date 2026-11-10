-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_greedy_properties
-- name    : MultiPartyError1146.Adaptive.greedy_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:34:25.860203+00:00
-- url     : https://prove2.me/theorems/e0d02be1-c4ee-43af-bbb5-d4f2a8b462e1
-- title:
--   Lemma 5.2 — all three greedy isolation properties
-- statement:
--   Fix a positive duration $T$ and an integer $1\le k<n/2$. The finite greedy construction terminates with a target $i^*\notin Q$. Its sets satisfy all three conclusions:
--   $$|P|\le2k,\qquad |S_{i^*,b}\cap\operatorname{supp}(Z)|\le T/k\quad(b=0,1).$$
--   For every round outside $\operatorname{supp}(Z)$, two distinct parties in $Q$ speak on their fixed private inputs and all-erasure prefixes. Because the operational attack erases their entire received transcripts, these are also their actions under that attack. Thus the third clause states actual distinct colliding speakers, not merely one speaking party.
--
--   Differences from the source:
--   - encoding: partial input/adversary on Q and arbitrary choices → total private-bit assignment extending the chosen values and lexicographic tie breaking; all-erasure speaking sets; reason: chosen parties receive only erasures, so their actions are independent of any extension
--   - encoding: multiset Z and subtraction by S → multiplicity function, minimum-multiplicity intersection and decrement by one; reason: each S has multiplicity one, exactly as the source proof on p.31 states
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 5.2, printed p.31, PDF p.33

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Attack

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem greedy_properties (n T k : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (hk : 1 ≤ k ∧ 2 * k < n) (P : Protocol n 1 T) :
    ∃ i : Fin n, target P k = some i ∧ i ∉ (greedy P k).chosen ∧
      (erasedParties P k).card ≤ 2 * k ∧
      (∀ b : Bool, ((silentSpeaking P i b ∩ remainingRounds P k).card : ℝ) ≤ (T : ℝ) / k) ∧
      (∀ t : Fin T, t ∉ remainingRounds P k →
        ∃ j₁ ∈ (greedy P k).chosen, ∃ j₂ ∈ (greedy P k).chosen,
          j₁ ≠ j₂ ∧ t ∈ silentSpeaking P j₁ ((greedy P k).input j₁) ∧
          t ∈ silentSpeaking P j₂ ((greedy P k).input j₂)) := by sorry

end MultiPartyError1146.Adaptive
