-- Prove2me | Theorems.Thm_OppenheimRelay_merging_ebit_gain
-- name    : OppenheimRelay.merging_ebit_gain
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:00.107713+00:00
-- url     : https://prove2.me/theorems/e4fd0a6c-c9b4-411b-a66d-e9866d458808
-- title:
--   Ebit gain of coherent merging: $-S(A\mid B)+\tfrac12 I(A:R)=\tfrac12 I(A:B)$
-- statement:
--   Let $A$, $B$, $R$ be finite-dimensional registers and $|\phi\rangle_{RAB}$ a pure state. Then
--   $$
--   -S(A\mid B)+\tfrac12\,I(A:R)=\tfrac12\,I(A:B).
--   $$
--
--   This is the ebit accounting of coherent state merging. State merging consumes $nS(A\mid B)$ ebits (it produces them when $S(A\mid B)<0$). Doing the measurement of merging coherently generates $nI(A:R)/2$ additional ebits. The identity says that, added together, the net gain is $nI(A:B)/2$ ebits. The relay protocol applies this count twice: merging $A$ to Charlie (with Bob's $B$ absorbed into the reference) and the final merging step to Bob.
--
--   The statement is per copy and states only the count. The protocol that achieves it, coherent merging (the fully quantum Slepian–Wolf protocol), is a separate open target on the platform.
--
--   Differences from the source:
--   - reading: "Adding these generated ebits to the initial nS(A|B), yields a total gain of nI(A : B)/2 ebits" → -S(A|B) + I(A:R)/2 = I(A:B)/2 for every pure state on R, A, B; reason: the initial nS(A|B) is the ebit cost of merging, consumed (previous paragraph of p.1), so it enters with a minus sign; only the count is stated, because the protocol achieving it is coherent merging, Open on the platform as Dependency50.P19.memorylessMother
--   - encoding: n copies → per copy (both sides divided by n); reason: every term is linear in n
--   - encoding: arbitrary registers, entropies in bits → finite nonempty index types, vnEntropy in base 2; reason: the paper works with qubits and finite states; a unit vector needs a nonempty basis
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraph "Now, to perform merging with a quantum channel…", last two sentences

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_mergeCondEntropy
import Definitions.Def_OppenheimRelay_mergeMiA_R
import Definitions.Def_OppenheimRelay_mergeMiA_B

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **The ebit gain of coherent merging.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph "Now, to perform merging…":
"Adding these generated ebits to the initial nS(A|B), yields a total gain of nI(A : B)/2 ebits".
For a pure state on R, A, B, per copy: `−S(A|B) + ½I(A:R) = ½I(A:B)`.

**Formalization Note** The "initial nS(A|B)" is the merging cost, in ebits consumed (previous
paragraph of p.1), so it enters with a minus sign. Only the count is stated: the operational half,
coherent merging, is the platform's Open `Dependency50.P19.memorylessMother`. -/
theorem merging_ebit_gain {A B R : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype R] [Nonempty R] (phi : EuclideanSpace ℂ (MergeSource A B R)) (hphi : IsState phi) :
    -mergeCondEntropy phi + mergeMiA_R phi / 2 = mergeMiA_B phi / 2 := by sorry

end OppenheimRelay
