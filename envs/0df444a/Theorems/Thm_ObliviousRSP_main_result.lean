-- Prove2me | Theorems.Thm_ObliviousRSP_main_result
-- name    : ObliviousRSP.main_result
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:12.732994+00:00
-- url     : https://prove2.me/theorems/6a1be462-3b10-46f8-a255-13457f41954a
-- title:
--   Main result — a faithful RSP protocol oblivious to Bob can be made oblivious to Alice
-- statement:
--   Let $S$ be a generic ensemble of pure states of $\mathbb C^d$, and let $(E,V,p,b)$ be a remote state preparation protocol for $S$ that uses only forward classical communication and the maximally entangled state $|\Phi_{d'}\rangle$, and is faithful and oblivious to Bob. Then there is a single measurement $\{M_m\}_{m\in M}$ (a POVM on the specimen and Alice's half), with the same message set and not depending on the state to be prepared, such that for every $\psi\in S$, with $\varphi = |\psi\rangle\langle\psi|$, and every message $m$,
--   $$
--   \operatorname{Tr}_{12}\big[(\varphi_1\otimes|\Phi_{d'}\rangle\langle\Phi_{d'}|_{23})(M_{m,12}\otimes I_3)\big] = p_m\,\rho_{\varphi m} .
--   $$
--
--   In words: Alice can replace her knowledge of $\varphi$ by a single specimen of it. Each message then occurs with the same probability $p_m$ and leaves Bob in the same state $\rho_{\varphi m}$, so his unchanged recovery still outputs $\varphi\otimes b_m$, and the classical communication is unchanged. The paper derives from this that such protocols need at least as much classical communication as teleportation, which is Lo's conjecture under these conditions.
--
--   **Formalization Note** Obliviousness to Alice is the quantifier order: the POVM is chosen before $\psi$. The single specimen is the domain of $M_m$, $\mathbb C^d\otimes\mathbb C^{d'}$. Bob's states are unnormalized (`modifiedBobState`, `bobState`), so their equality also fixes the message probabilities.
--
--   Differences from the source:
--   - reading: oblivious to Bob (p.2: Bob obtains no more information than the single specimen) → p_m and b_m^(out) do not depend on φ; reason: this is the consequence the paper draws from the oblivious condition on p.3 and the only form in which the proof uses it
--   - reading: "a general ensemble of pure states" in the claim → a generic ensemble (IsGeneric S); reason: "generic ensemble" is defined in the sentence before the claim and the proof uses exactly it (p.3); the paper's latitude example (pp.5–6) shows the claim fails for non-generic ensembles
--   - generalization: generic ensemble: the density matrices form a basis of the operators on the input space → IsGeneric S: unit vectors whose projectors span all ι × ι matrices; reason: every basis spans, so every generic ensemble of the paper satisfies IsGeneric
--   - generalization: Bob's recovery: unitary U_m on his half and a pure ancilla |0⟩ → any isometry V_m : ℂ^σ → ℂ^ι ⊗ ℂ^{K m}, with an output space K m per message, and no Tr_2; reason: U_m(· ⊗ |0⟩) is an isometry, so the paper's protocols are instances; for an isometry nothing is left over to trace
--   - generalization: sum over the messages m → HasSum over an arbitrary message type M; reason: covers finite and countably infinite message sets (p.5 allows messages of variable length); for a finite M it is the finite sum
--   - encoding: Alice's trace-preserving operation E_φ with classical output m → a POVM E ψ on her half with outcome type M; reason: the paper's own reduction on p.2: with only classical output, E_φ is a POVM
--   - encoding: normalized conditional state ρ_φm → unnormalized p_m ρ_φm (bobState (E ψ m)); reason: ρ_φm is undefined when p_m = 0; for p_m > 0 dividing by p_m gives the page's identity, and the unnormalized state is the paper's own b of (6); same instances
--   - encoding: "at no extra classical communication cost" → the modified measurement has the same message set M, and each message has the same probability p_m (equal unnormalized states have equal traces); reason: the same messages with the same distribution have the same cost in every cost measure (p.4, first observation)
--   - reading: "uses only forward communication and entanglement" → the shared entangled state is |Φ_d′⟩ (maxEnt σ, Alice's half first); reason: the paper fixes this model for the claim's protocols on p.2 ("the entangled state shared by Alice and Bob is a maximally entangled state in 2 d′-dimensional systems"); the proof uses it in (2) and (6)
--   - generalization: Alice's operation E_φ parameterized by the pure state φ → E ψ parameterized by a vector ψ with φ = |ψ⟩⟨ψ|; reason: every protocol of the paper is an instance (E ψ := E_φ for φ = |ψ⟩⟨ψ|); E may in addition depend on the global phase of ψ
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, main result (italic claim), p.2; proof pp.2–4

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ObliviousRSP_IsPOVM
import Definitions.Def_ObliviousRSP_bobState
import Definitions.Def_ObliviousRSP_IsObliviousRSP
import Definitions.Def_ObliviousRSP_IsGeneric
import Definitions.Def_ObliviousRSP_modifiedBobState

open scoped Kronecker Matrix

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, main result, p.2: "If an RSP protocol for a general ensemble of pure states uses only
forward communication and entanglement, and is faithful and oblivious to Bob, then it can be
modified to be oblivious to Alice at no extra classical communication cost."

Let `S` be a generic ensemble of pure states of `ℂ^ι` and let `(E, V, p, b)` be a faithful
remote state preparation protocol for `S` that uses only forward classical communication and the
maximally entangled state `|Φ_{d′}⟩`, and is oblivious to Bob (`IsObliviousRSP`). Then there is a
**single** POVM `{M_m}` on the specimen `φ` and Alice's half, with the same message set and not
depending on `φ`, such that for every `ψ ∈ S` and every message `m` Bob's unnormalized state after
outcome `m` is the same as in the original protocol. Hence `m` has the same probability `p_m`, Bob
holds the same state `ρ_φm`, and his unchanged recovery `V m` outputs `φ ⊗ b_m`, with the same
classical messages.

**Formalization Note.** Obliviousness to Alice is the quantifier order: the POVM `Mod` is chosen
before `ψ`. A single specimen: `Mod m` acts on `ι × σ` only. Bob's states are unnormalized
(`bobState`, `modifiedBobState`), so equality also fixes the outcome probabilities. -/
theorem main_result {ι σ M : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {K : M → Type} [∀ m, Fintype (K m)] [∀ m, DecidableEq (K m)]
    {S : Set (ι → ℂ)} {E : (ι → ℂ) → M → Matrix σ σ ℂ} {V : (m : M) → Matrix (ι × K m) σ ℂ}
    {p : M → ℝ} {b : (m : M) → Matrix (K m) (K m) ℂ}
    (hS : IsGeneric S) (h : IsObliviousRSP S E V p b) :
    ∃ Mod : M → Matrix (ι × σ) (ι × σ) ℂ, IsPOVM Mod ∧
      ∀ ψ ∈ S, ∀ m, modifiedBobState (Mod m) (pureState ψ) = bobState (E ψ m) := by sorry

end ObliviousRSP
