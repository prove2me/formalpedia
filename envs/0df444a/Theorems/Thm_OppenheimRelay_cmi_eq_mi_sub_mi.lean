-- Prove2me | Theorems.Thm_OppenheimRelay_cmi_eq_mi_sub_mi
-- name    : OppenheimRelay.cmi_eq_mi_sub_mi
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:08.405759+00:00
-- url     : https://prove2.me/theorems/5ea707bb-9ef7-48ff-b37c-ed41e749f7b4
-- title:
--   Qubits the relay still sends (corrected: ½ on the left): $\tfrac12 I(A:R\mid B)=\tfrac12 I(A:RC)-\tfrac12 I(A:C)$
-- statement:
--   Let $A$, $C$, $B$, $R$ be finite-dimensional registers and $|\psi\rangle_{RACB}$ a pure state. Then
--   $$
--   \tfrac12\,I(A:R\mid B)=\tfrac12\,I(A:RC)-\tfrac12\,I(A:C).
--   $$
--
--   In the relay protocol, a naive coherent merging of $A$ to Bob would send $nI(A:RC)/2$ qubits; the ebit repackaging of steps 1a–2 is equivalent to Alice having already sent $nI(A:C)/2$ of them. The identity says that what remains to be sent from Charlie to Bob is exactly the Devetak–Yard rate $\tfrac12 I(A:R\mid B)$ per copy, the value $Q^{C\to B}$ of the paper's rate display.
--
--   The paper prints the identity without the factor $\tfrac12$ on the left, which makes it false (see below). The corrected form agrees with the rate display, with step 3 of the protocol, and with p.1 ("using $nI(A:R|B)/2$ qubits", "a saving of $nI(A:C)/2$ qubits").
--
--   Differences from the source:
--   - correction: nI(A : R|B) = nI(A : RC)/2 − nI(A : C)/2 → I(A:R|B)/2 = I(A:RC)/2 − I(A:C)/2; reason: the printed identity is false: for ψ = |φ+⟩_AR ⊗ |0⟩_C ⊗ |0⟩_B (one qubit each) I(A:R|B) = 2, I(A:RC) = 2, I(A:C) = 0, so the left side is 2n and the right side n for every n ≥ 1; the ½ matches the rate display Q^{C→B} = ½I(A:R|B), step 3 and p.1
--   - encoding: n copies → per copy (both sides divided by n); reason: every term is linear in n
--   - encoding: arbitrary registers, entropies in bits → finite nonempty index types, vnEntropy in base 2; reason: the paper works with qubits and finite states; a unit vector needs a nonempty basis
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.2, paragraph after the protocol box ("Since a naive coherent-merging protocol requires…")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_cmiA_R_B
import Definitions.Def_OppenheimRelay_miA_RC
import Definitions.Def_OppenheimRelay_miA_C

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **The qubits Charlie still sends (corrected: ½ on the left).** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.2, paragraph after the
protocol box: "all that remains to be sent are nI(A : R|B) = nI(A : RC)/2 − nI(A : C)/2 qubits".
For a pure state on R, A, C, B, per copy: `½I(A:R|B) = ½I(A:RC) − ½I(A:C)`.

**Formalization Note** The printed identity lacks the ½ on the left, and it is false as printed: at
`|φ+⟩_AR ⊗ |0⟩_C ⊗ |0⟩_B` one has `I(A:R|B) = 2`, `I(A:RC) = 2`, `I(A:C) = 0`. The corrected form
agrees with the display (`Q^{C→B} = ½I(A:R|B)`), step 3, and p.1. -/
theorem cmi_eq_mi_sub_mi {A C B R : Type*} [Fintype A] [Nonempty A]
    [Fintype C] [Nonempty C] [Fintype B] [Nonempty B] [Fintype R] [Nonempty R]
    (psi : EuclideanSpace ℂ (RelaySource A C B R)) (hpsi : IsState psi) :
    cmiA_R_B psi / 2 = miA_RC psi / 2 - miA_C psi / 2 := by sorry

end OppenheimRelay
