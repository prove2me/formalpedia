-- Prove2me | Theorems.Thm_OppenheimRelay_relay_redistribution
-- name    : OppenheimRelay.relay_redistribution
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:33:36.747897+00:00
-- url     : https://prove2.me/theorems/80e1f153-53ff-488f-a77f-6ba26165ce0e
-- title:
--   Coherent relay: rates $(\tfrac12 I(A:RB),\,-\tfrac12 I(A:C),\,\tfrac12 I(A:R\mid B),\,\tfrac12 I(A:C)-\tfrac12 I(A:B))$ are achievable, and the Charlie–Bob pair is optimal
-- statement:
--   Let $A$, $C$, $B$, $R$ be finite-dimensional registers and $|\psi\rangle_{RACB}$ a pure state, with Alice holding $A$, the relay Charlie holding $C$, Bob holding $B$, and $R$ the reference. Write $Q^{A\to C}$ and $Q^{C\to B}$ for the qubit rates on the two links and $E^{AC}$, $E^{CB}$ for the net ebit consumption on them (negative: production).
--
--   1. **Achievability.** The tuple
--   $$
--   Q^{A\to C}=\tfrac12 I(A:RB),\quad E^{AC}=-\tfrac12 I(A:C),\quad
--   Q^{C\to B}=\tfrac12 I(A:R\mid B),\quad E^{CB}=\tfrac12 I(A:C)-\tfrac12 I(A:B)
--   $$
--   is achievable: for every error $\varepsilon>0$ and slack $\delta>0$, every large enough blocklength $n$ has one relay code (Alice → Charlie → Bob) that transfers $A^n$ to Bob with full-state trace-norm error at most $\varepsilon$, while meeting all four rates up to $\delta$ per copy.
--
--   2. **Optimality of the Charlie–Bob pair.** Every achievable tuple $(Q^{A\to C},E^{AC},Q^{C\to B},E^{CB})$ satisfies
--   $$
--   Q^{C\to B}\ge\tfrac12 I(A:R\mid B),\qquad Q^{C\to B}+E^{CB}\ge\tfrac12 I(A:R\mid B)+\tfrac12 I(A:C)-\tfrac12 I(A:B).
--   $$
--
--   The relay transfers Alice's share to Bob with exactly the qubits and ebits per copy that optimal two-party state redistribution (Devetak–Yard) needs on the Charlie–Bob link, although Charlie never holds $A$ when the protocol starts. In addition, the Alice–Charlie link ends with $\tfrac12 I(A:C)$ ebits per copy more than it started with. With Alice and Charlie co-located, the statement specializes to the Devetak–Yard achievability and converse.
--
--   Differences from the source:
--   - generalization: E^{AC} = ½I(A:C) ("consumed ebits") → E^{AC} = −½I(A:C), i.e. ½I(A:C) ebits per copy produced on the Alice–Charlie link; reason: steps 1b–2 generate these ebits and set them aside (Fig. 1: no Alice–Charlie ebit in panel 0, one in panel 3); RelayAchievable is monotone in each E, so the Lean tuple implies the printed one
--   - reading: "we have the optimal rate pairs" (no converse is proved; optimality is imported from [1]) → every achievable tuple has Q^{C→B} ≥ ½I(A:R|B) and Q^{C→B} + E^{CB} ≥ ½I(A:R|B) + ½I(A:C) − ½I(A:B); reason: co-locating Alice and Charlie turns any relay code into a two-party redistribution code, to which the converse of [1] applies; lower bounds on the Alice–Charlie pair are false (ψ = |φ+⟩_AB, C and R trivial: the code with no communication and no ebits, in which Bob prepares the target himself, achieves Q^{A→C} = E^{AC} = 0 < ½I(A:RB) = 1)
--   - encoding: "virtually unchanged (in terms of fidelity)" → trace norm of output minus target on the whole system (R^n, C^n, A^nB^n and both final Bell banks) at most ε; reason: fidelity → 1 iff trace distance → 0 (Fuchs–van de Graaf); the convention of the published Devetak–Yard layer
--   - encoding: rates per copy → RelayAchievable: ∀ ε δ > 0, ∃ N, ∀ n ≥ N with n ≥ 1, one relay code meets all four bounds with slack δ; reason: the standard asymptotic meaning of a rate, as in the published RedistributionAchievable; n ≥ 1 only excludes the empty blocklength
--   - encoding: n copies of a mixed ρ_ABC, purified by R → every unit vector ψ on R × (A × (C × B)) with finite nonempty index types; register order R, A, C, B; entropies in bits; reason: the paper's own device ("One imagines a total pure state |ψ⟩ABCR"); every purification is covered
--   - encoding: three-party protocol with Charlie acting as a relay station → sequential composition: Alice's channel, then Charlie's on her message, then Bob's on Charlie's message, messages transmitted as quantum registers; reason: no message flows backwards, so each party can postpone its operations until its incoming message has arrived
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.2, rate display after "Protocol: redistribution from merging", with the accounting sentence that introduces it

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_miA_RB
import Definitions.Def_OppenheimRelay_miA_C
import Definitions.Def_OppenheimRelay_miA_B
import Definitions.Def_OppenheimRelay_cmiA_R_B
import Definitions.Def_OppenheimRelay_RelayAchievable

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **The relay rate tuple.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.2, display after "Protocol: redistribution from merging":
"Accounting for sent qubits Q^{A→C} between Alice and Charlie and Q^{C→B} between Charlie and Bob,
as well as consumed ebits E_{AC} and E_{BC} we have the optimal rate pairs
Q^{A→C} = ½I(A : RB), E^{AC} = ½I(A : C); Q^{C→B} = ½I(A : R|B), E^{CB} = ½I(A : C) − ½I(A : B)".

First conjunct: one family of relay codes achieves all four rates at once, with
`E^{AC} = −½I(A:C)`. Second conjunct: every achievable tuple satisfies `½I(A:R|B) ≤ Q^{C→B}` and
`½I(A:R|B) + ½I(A:C) − ½I(A:B) ≤ Q^{C→B} + E^{CB}`.

**Formalization Note** The printed `E^{AC} = ½I(A:C)` counts ebits consumed, but steps 1b–2 and
Fig. 1 generate those ebits, so the Lean rate is `−½I(A:C)`, which implies the printed one because
`RelayAchievable` is monotone in each `E`. "Optimal" is read as the two lower bounds on the
Charlie–Bob pair: the paper proves no converse, and lower bounds on the Alice–Charlie pair are
false. -/
theorem relay_redistribution {A C B R : Type*} [Fintype A] [Nonempty A]
    [Fintype C] [Nonempty C] [Fintype B] [Nonempty B] [Fintype R] [Nonempty R]
    (psi : EuclideanSpace ℂ (RelaySource A C B R)) (hpsi : IsState psi) :
    RelayAchievable psi (miA_RB psi / 2) (-(miA_C psi / 2))
        (cmiA_R_B psi / 2) (miA_C psi / 2 - miA_B psi / 2) ∧
    ∀ qAC eAC qCB eCB : ℝ, RelayAchievable psi qAC eAC qCB eCB →
      cmiA_R_B psi / 2 ≤ qCB ∧
      cmiA_R_B psi / 2 + (miA_C psi / 2 - miA_B psi / 2) ≤ qCB + eCB := by sorry

end OppenheimRelay
