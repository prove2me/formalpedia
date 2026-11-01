-- Prove2me | Theorems.Thm_OppenheimRelay_charlie_leftover_qubits
-- name    : OppenheimRelay.charlie_leftover_qubits
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:49.673869+00:00
-- url     : https://prove2.me/theorems/bc704420-9263-46b2-a2a6-9ce0df9be618
-- title:
--   What the relay is left with: $\tfrac12 I(A:RB)-\big(\tfrac12 I(A:RC)-\tfrac12 I(A:C)\big)=\tfrac12 I(A:B)$
-- statement:
--   Let $A$, $C$, $B$, $R$ be finite-dimensional registers and $|\psi\rangle_{RACB}$ a pure state. Then
--   $$
--   \tfrac12\,I(A:RB)-\Big(\tfrac12\,I(A:RC)-\tfrac12\,I(A:C)\Big)=\tfrac12\,I(A:B).
--   $$
--
--   In step 1a of the relay protocol Charlie receives $nI(A:RB)/2$ qubits from Alice; in step 3 he sends the remaining $nI(A:CR)/2-nI(A:C)/2$ of them to Bob. The identity says that he is left with $nI(A:B)/2$ qubits, which the paper observes are ebits between him and Bob. This count is the source of the term $-\tfrac12 I(A:B)$ in the rate $E^{CB}$ of the display.
--
--   $I(A:CR)$ and $I(A:RC)$ denote the same quantity. Only the count is stated; that the leftover qubits are ebits with Bob is part of the relay goal, whose target state contains the final Charlie–Bob Bell pairs.
--
--   Differences from the source:
--   - reading: "Charlie then sends the remaining nI(A : CR)/2 − nI(A : C)/2 qubits … This leaves him with nI(A : B)/2 qubits" → I(A:RB)/2 − (I(A:RC)/2 − I(A:C)/2) = I(A:B)/2 for every pure state on R, A, C, B; reason: the qubits Charlie holds are the nI(A:RB)/2 received in step 1a; the step states a count, which is this identity; the operational part (they are ebits with Bob) is required by the goal's target state
--   - encoding: n copies → per copy (both sides divided by n); reason: every term is linear in n
--   - encoding: arbitrary registers, entropies in bits → finite nonempty index types, vnEntropy in base 2; reason: the paper works with qubits and finite states; a unit vector needs a nonempty basis
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.2, protocol step 3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_miA_RB
import Definitions.Def_OppenheimRelay_miA_RC
import Definitions.Def_OppenheimRelay_miA_C
import Definitions.Def_OppenheimRelay_miA_B

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **What Charlie is left with.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.2, protocol step 3: "Charlie then sends the remaining
nI(A : CR)/2 − nI(A : C)/2 qubits needed to transfer ρA to Bob. This leaves him with nI(A : B)/2
qubits". For a pure state on R, A, C, B, per copy: of the `½I(A:RB)` qubits Charlie received in
step 1a, sending `½I(A:RC) − ½I(A:C)` leaves `½I(A:B)`.

**Formalization Note** `I(A:CR)` and `I(A:RC)` are the same quantity, `miA_RC`. That the leftover
qubits "are in fact ebits" is operational, and the goal's `RelayCode.target` requires it. -/
theorem charlie_leftover_qubits {A C B R : Type*} [Fintype A] [Nonempty A]
    [Fintype C] [Nonempty C] [Fintype B] [Nonempty B] [Fintype R] [Nonempty R]
    (psi : EuclideanSpace ℂ (RelaySource A C B R)) (hpsi : IsState psi) :
    miA_RB psi / 2 - (miA_RC psi / 2 - miA_C psi / 2) = miA_B psi / 2 := by sorry

end OppenheimRelay
