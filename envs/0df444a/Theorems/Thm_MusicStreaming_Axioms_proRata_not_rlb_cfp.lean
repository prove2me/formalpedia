-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_proRata_not_rlb_cfp
-- name    : MusicStreaming.Axioms.proRata_not_rlb_cfp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:18.724149+00:00
-- url     : https://prove2.me/theorems/7aa49bd0-6a59-409c-bf59-643d1b2550e6
-- title:
--   §3, p. 13; Appendix, pp. 21–22 — with at least two artists, pro-rata violates reasonable lower bound and click-fraud-proofness
-- statement:
--   Let there be at least two artists. The pro-rata index $P_i=T_i$ satisfies neither reasonable lower bound nor click-fraud-proofness.
--
--   The paper shows both failures on Example 1 (two artists; user $a$ streams artist 1 ten times, user $b$ streams artist 2 ninety times): for $C=\{a\}$ the reward of $L^a=\{1\}$ is $\frac{10}{100}\cdot 2<1$, and changing $b$'s streams to $2$ moves artist 2's reward by $\frac{22}{15}>1$.
--
--   **Formalization Note** The paper's counterexamples have two artists; the statement is for every number $n\ge 2$ of artists (with one artist every index pays the whole $m$ to that artist, and both axioms hold).
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 13 (claim after click-fraud-proofness) and pp. 21–22, Appendix, the two paragraphs on the pro-rata index

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem proRata_not_rlb_cfp {n : ℕ} (hn : 2 ≤ n) :
    ¬ ReasonableLowerBound (proRata (n := n)) ∧ ¬ ClickFraudProof (proRata (n := n)) := by sorry

end MusicStreaming.Axioms
