-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_identical_transcripts
-- name    : MultiPartyError1146.Adaptive.identical_transcripts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:34:22.436117+00:00
-- url     : https://prove2.me/theorems/811c5c5b-c6de-4eed-b7d1-ac8f081a1e2b
-- title:
--   Lemma 5.3 — identical received transcripts
-- statement:
--   Let the inputs away from the chosen target $i^*$ be any extension of the greedy assignment on $Q$. Run the operational party/round erasure policy with the target's private bit first 0 and then 1. Every received coordinate at every party is identical:
--   $$A_{x_{i^*}=0}(t,j)=A_{x_{i^*}=1}(t,j)\quad\text{for all }t,j.$$
--   Only received transcripts are equated. The target's private input and its own output need not agree. An outside receiver has the same private input and hence cannot recover both full input vectors correctly.
--
--   Differences from the source:
--   - encoding: the same adversary A on two inputs → the same recursive mask policy, evaluated on each input, yields equal received matrices; reason: the actual delivered baseline is computed separately in each execution
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 5.3, printed p.32, PDF p.34

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Attack

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem identical_transcripts (n T k : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (hk : 1 ≤ k ∧ 2 * k < n) (P : Protocol n 1 T) (i : Fin n)
    (hi : target P k = some i) (x : Input n 1)
    (hx : ∀ j ∈ (greedy P k).chosen, x j 0 = (greedy P k).input j) :
    isolationAttack P k (Function.update x i (fun _ => false)) =
      isolationAttack P k (Function.update x i (fun _ => true)) := by sorry

end MultiPartyError1146.Adaptive
