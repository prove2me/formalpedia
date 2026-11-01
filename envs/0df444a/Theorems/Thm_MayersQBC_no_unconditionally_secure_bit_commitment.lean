-- Prove2me | Theorems.Thm_MayersQBC_no_unconditionally_secure_bit_commitment
-- name    : MayersQBC.no_unconditionally_secure_bit_commitment
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:27:17.544323+00:00
-- url     : https://prove2.me/theorems/12c781d2-7a71-41d5-a788-4116acd2eaf8
-- title:
--   Section e, pp.3–4 — no quantum bit commitment is unconditionally secure: concealing implies Alice unveils 1 after committing to 0 with probability → 1
-- statement:
--   Consider a quantum bit commitment protocol with security parameter $n$, starting from the all-$|0\rangle$ state. For each $n$, let $\Gamma_n$ be the finite set of classical transcripts $\gamma$ stored in the public register after Alice's modified commitment commit′ (she commits to $0$ honestly but never sends a register away to the environment except for classical messages), $p_n$ their law when Alice commits to $0$ and $q_n$ their law when she commits to $1$. Let $\psi'_{0,\gamma}, \psi'_{1,\gamma}$ be the resulting pure states (unit vectors) of Alice's side $A_n$ and Bob's side $B_n$, and let $\Pi_{n,\gamma}$ be an effect ("the honest unveil of $1$ returns $1$") that accepts $\psi'_{1,\gamma}$ with certainty whenever $q_n(\gamma) \ne 0$ (correctness). Write
--
--   $$
--   \mathbb E_\gamma F'(\gamma) = \sum_{\gamma\in\Gamma_n} p_n(\gamma) F'(\gamma), \qquad F'(\gamma) = \begin{cases} 0 & q_n(\gamma) = 0,\\ F\big(\rho_B(\psi'_{0,\gamma}),\rho_B(\psi'_{1,\gamma})\big) & \text{otherwise,}\end{cases}
--   $$
--
--   with $F$ Jozsa's fidelity of Bob's reduced states. If the protocol is concealing,
--
--   $$
--   \lim_{n\to\infty} \mathbb E_\gamma F'(\gamma) = 1,
--   $$
--
--   then there are unitaries $U_{n,\gamma}$ on Alice's side such that Alice's probability of unveiling $1$ after the honest commitment to $0$,
--
--   $$
--   P^{\mathrm{cheat}}_n = \sum_{\gamma\in\Gamma_n} p_n(\gamma)\,\big\langle\psi'_{0,\gamma}\big|(U_{n,\gamma}\otimes I)^\dagger\,\Pi_{n,\gamma}\,(U_{n,\gamma}\otimes I)\big|\psi'_{0,\gamma}\big\rangle,
--   $$
--
--   satisfies $P^{\mathrm{cheat}}_n \ge \mathbb E_\gamma F'(\gamma)$ for every $n$, and $P^{\mathrm{cheat}}_n \to 1$. Hence the commitment is not binding: no quantum bit commitment protocol that starts in this state is unconditionally secure.
--
--   **Formalization Note** Alice's side is the first tensor factor (`traceLeft` gives Bob's state; Alice acts by `Matrix.kronecker (U n γ) 1`). $F$ is `rootFidelity ^ 2`. The honest unveil of $1$ is one effect per transcript. The first two steps of the paper's proof (commit′, Bob's commit″ and their formal identity) are the modelling argument that turns security against Bob into the hypothesis $\mathbb E_\gamma F'(\gamma) \to 1$.
--
--   Differences from the source:
--   - reading: "binding" (section c: arbitrarily close to perfectly binding), for which the paper gives no quantitative definition → the conclusion states the attack: after an honest commitment to 0, unveil′ returns 1 with probability ≥ E_γ F′(γ) and → 1; reason: the honest unveil of a commitment to 0 never returns 1, so this contradicts every reading of binding; it is the sentence with which the proof ends
--   - reading: first and second steps of the proof: security against Bob makes the expected value of F′(γ) arbitrarily close to 1 → hypothesis hconceal: Tendsto (expectedFidelity) atTop (𝓝 1); reason: steps one and two are a modelling argument about commit′ and commit″ that the paper does not formalize; their conclusion is the hypothesis of the third step, and "goes to 1 as the expected value goes to 1" is a statement about limits in n
--   - reading: the expected value of F′(γ) under commit′ → the expectation under the transcript law p n of a commitment to 0; reason: in commit′ Alice chooses b = 0, and the transcript law of commit′ equals that of the honest commitment to 0 ("formally identical")
--   - generalization: the cheating probability goes to 1 → the limit together with the explicit bound cheat ≥ E_γ F′(γ) for every n; reason: the bound is an additional true clause; dropping it gives the paper's limit statement
--   - generalization: one quantum bit commitment protocol in the model of section b → arbitrary finite types Γ, A, B, any transcript laws p, q, any unit vectors ψ0 γ, ψ1 γ and any effects acc γ; reason: every protocol of the model yields such data (finite register spaces, a finite transcript set, the honest unveil of 1 composed with Bob's verdict is an effect for each transcript), so the protocol is a special case
--   - generalization: q is the law of the transcript under commit(1) → q is any real function; only its zero set is used; reason: the transcript law under commit(1) is one such function
--   - encoding: F′(γ) = 0 when γ determines a single value of the bit b (section c) → the term of γ is 0 when q γ = 0; reason: a transcript with p γ > 0 determines b exactly when it cannot occur under commit(1), i.e. q γ = 0; a transcript with p γ = 0 carries weight 0
--   - encoding: registers whose number differs between transcripts, in linear superposition → fixed finite types A, B for all transcripts; reason: unused registers are padded in the fixed state |0⟩; this changes no probability
--   - reading: correctness: "unveil always return b on |ψb⟩ when both participants are honest" (section c), used on the purified states ψ′1,γ ("then continue with the honest unveil") → hypothesis: the effect acc γ accepts ψ1 γ with probability 1 whenever q γ ≠ 0; reason: honest Alice's unveil acts on her own registers, so keeping her private registers (commit′) instead of decohering them does not change Bob's verdict; correctness is meaningful only for transcripts that can occur under commit(1)
--   - encoding: the fidelity [9] (Jozsa) F(ρ, σ) = (Tr √(√ρ σ √ρ))² → QAlgorithms.rootFidelity ρ σ ^ 2; reason: rootFidelity is Tr √(√ρ σ √ρ); its square is Jozsa's fidelity, the one the paper cites
--   - encoding: H_A ⊗ H_B with Alice's side H_A → EuclideanSpace ℂ (A × B) with Alice's side the first factor A; traceLeft gives Bob's reduced state and Alice acts by Matrix.kronecker U 1; reason: fixed ordering convention of the published traceLeft; it changes no instance
-- source:
--   Mayers, Unconditionally secure quantum bit commitment is impossible, arXiv:quant-ph/9605044v2, section e, pp.3–4 (headline sentence, p.3; conclusion of the third step, p.4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_MayersQBC_expectedFidelity
import Definitions.Def_MayersQBC_cheatProb
open QAlgorithms Filter Topology

namespace MayersQBC

/-- Mayers, *Unconditionally secure quantum bit commitment is impossible*,
arXiv:quant-ph/9605044v2, section e, pp.3–4. Headline (p.3): "We prove that no quantum bit
commitment protocol that starts in this state is unconditionally secure"; conclusion of the third
step (p.4): "This means that Alice can change the bit b that she unveils to Bob from 0 to 1 with
a probability that goes to 1 as the expected value of F′(γ) goes to 1."

For every security parameter `n`: `Γ n` is the finite set of classical transcripts `γ` stored
after commit′, `p n` their law when Alice commits to `0`, `q n` their law when she commits to `1`;
`ψ0 n γ, ψ1 n γ` are the pure states `ψ′_{0,γ}, ψ′_{1,γ}` of Alice's side `A n` and Bob's side
`B n` (`H_B ⊗ H_{E,B}`) after commit′; `acc n γ` is the effect "the honest unveil of `1` returns
`1`", correct on `ψ1 n γ` whenever `γ` can occur under a commitment to `1`. If the protocol is
concealing in the sense that the expected fidelity `E_γ F′(γ)` of Bob's reduced states tends to
`1`, then there are unitaries `U n γ` on Alice's side such that, for every `n`, Alice's
probability of unveiling `1` after an honest commitment to `0` (apply `U n γ`, then unveil `1`
honestly) is at least `E_γ F′(γ)`, and this probability tends to `1`.

**Formalization Note.** Alice's register is the **first** tensor factor (`A n × B n`;
`traceLeft` gives Bob's state; Alice acts by `Matrix.kronecker (U n γ) 1`). `F′` is Jozsa's
fidelity `rootFidelity ^ 2`, set to `0` when `q n γ = 0` ("γ determines b", section c). The honest
unveil of `1` is one effect per transcript. Registers whose number varies with `γ` are padded
into the fixed finite types `A n`, `B n`. Steps one and two of the proof (commit′ and commit″)
are the modelling argument that turns security against Bob into the hypothesis `hconceal`. -/
theorem no_unconditionally_secure_bit_commitment
    (Γ A B : ℕ → Type) [∀ n, Fintype (Γ n)] [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
    [∀ n, Fintype (B n)] [∀ n, DecidableEq (B n)]
    (p q : ∀ n, Γ n → ℝ) (hp : ∀ n, (∀ γ, 0 ≤ p n γ) ∧ ∑ γ, p n γ = 1)
    (ψ0 ψ1 : ∀ n, Γ n → EuclideanSpace ℂ (A n × B n))
    (h0 : ∀ n γ, IsState (ψ0 n γ)) (h1 : ∀ n γ, IsState (ψ1 n γ))
    (acc : ∀ n, Γ n → Matrix (A n × B n) (A n × B n) ℂ) (hacc : ∀ n γ, IsEffect (acc n γ))
    (hcorrect : ∀ n γ, q n γ ≠ 0 → effectProb (acc n γ) (pureDensity (ψ1 n γ)) = 1)
    (hconceal : Tendsto (fun n => expectedFidelity (p n) (q n) (ψ0 n) (ψ1 n)) atTop (𝓝 1)) :
    ∃ U : ∀ n, Γ n → Matrix (A n) (A n) ℂ, (∀ n γ, U n γ ∈ Matrix.unitaryGroup (A n) ℂ) ∧
      (∀ n, expectedFidelity (p n) (q n) (ψ0 n) (ψ1 n) ≤ cheatProb (p n) (acc n) (U n) (ψ0 n)) ∧
      Tendsto (fun n => cheatProb (p n) (acc n) (U n) (ψ0 n)) atTop (𝓝 1) := by sorry

end MayersQBC
