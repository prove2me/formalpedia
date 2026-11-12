-- Prove2me | Theorems.Thm_FourMsgQMA_base_protocol_bkl22
-- name    : FourMsgQMA.base_protocol_bkl22
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:34:08.618349+00:00
-- url     : https://prove2.me/theorems/11e5dcf7-82b3-4b76-862b-4cd96495898a
-- title:
--   §3.4 / §4.1 — the base protocol from LWE [BKL+22, Theorem 10.4]
-- statement:
--   This is the base-protocol instantiation of §3.4 and §4.1 ([BKL+22, Theorem 10.4]) in the pinned-down version requested by the operator.
--
--   Fix $\varepsilon\in(0,1)$ and assume $\mathrm{Hyp}(\varepsilon)$. Let $L$ be a QMA promise problem with verification family $F$. Then $L$ has a four-message base protocol $\Pi_0=(\mathrm{Gen},P_1,P_2,V)$ with all of the following properties:
--
--   1. setup $\mathrm{Gen}(1^\lambda,T)$ independent of the instance;
--   2. a uniform challenge $c\in\{0,1\}^{m(\lambda,T)}$;
--   3. polynomial-time algorithms, with all sizes $\mathrm{poly}(\lambda,T)$;
--   4. overwhelming statistical completeness for the resource $W_0(x)$, which is $N(\lambda,T)$ copies of any witness in $W_Q(x,2/3)$;
--   5. negligible soundness, Definition 3.7 with $s_0=0$: for fixed $x_\lambda\in L_{\mathrm{no}}$ and every QPT $(A_1,A_2)$,
--   $$
--   \Pr\big[V(x,r,\mu,c,z)=1\big]\le\nu(\lambda).
--   $$
--
--   The source states this as: "The ordinary-key CM–FHM construction, specialized to one instance, realizes the amplified input-independent batch interface under its LWE assumption". It is the base protocol $\Pi_0$ run at every selected coordinate of the construction of §5.1. Its negligible soundness absorbs the $1/k$ loss of the reduction.
--
--   Differences from the source:
--   - reading: "under its LWE assumption [BKL+22, Theorem 10.4]" → Hyp(ε) for the given ε ∈ (0,1): LWE (Assumption 3.10's game) for every efficiently computable (n, q, σ) with polynomial n ≥ max(λ,1), 2 ≤ q ≤ 2^{n^ε}, discrete Gaussian error D_{ℤ,σ} with σ ≥ 2√n; reason: the paper fixes no family ("Each instantiation specifies its family", p.15); it keeps a superpolynomial modulus-to-noise ratio (p.14) and GSW needs q > 8(M+1)^L B with dimension and log q polynomial (p.18), i.e. ratio 2^{poly}; σ ≥ 2√n is Regev's regime
--   - reading: "realizes the amplified input-independent batch interface" → a BaseProtocol with input-independent Gen(1^λ, T), uniform challenge, the size bounds of §3.4, overwhelming statistical completeness and negligible soundness; reason: p.13: "In the batch construction, s0 = 0 and ε0 is negligible"; §4.1: "Its public challenge c is the entire challenge vector"
--   - reading: W0(x): "Honest witnesses and their copy count are part of W0" → N(λ, T) copies of any density operator ρ ∈ W_Q(x, 2/3), N polynomial and chosen by the protocol; reason: the QMA threshold of p.10; completeness required for every such witness
--   - encoding: the local resource parameter T → T = t_L(x) = |x| + witness + ancilla wires + 1 + depth of Q_x; reason: T is polynomial in λ and the cost of one QMA verification (p.9)
--   - reading: "All messages, the state r, and the circuit for V have fixed size bounds poly(λ, T)" → one polynomial bounds |p|, |r|, m, N, the honest core and every honest response µ, z, the accepted responses (V rejects longer µ, z), and V is computed by circuits of that size on the inputs that occur; reason: worst-case size bounds of §3.3, p.12
--   - reading: PPT / deterministic classical algorithms and their running times → QAlgorithms.Complexity.PolyTimeComputable maps of the packed inputs with explicit uniform coins; per-instance work as Boolean circuit size (ComputedOn); reason: the paper's machine model is informal (§3.3); this is the standard uniform model
--   - encoding: QPT adversaries and distinguishers: nonuniform polynomial-size quantum circuit families with one quantum advice state (§3.1, p.9) → the published TightPQRepetition.Main.IsQPT strategies and IsQTestFamily distinguishers (gate set: all one- and two-qubit unitaries), on both sides of the implication; reason: a finite universal gate set approximates these circuits to negligible error at polynomial cost (Solovay–Kitaev), so the classes give the same negligible-advantage statements
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.4, p.14 (PDF 16) and §4.1, p.26 (PDF 28); Definition 3.7, p.13

import Mathlib
import Definitions.Def_FourMsgQMA_LWEHyp
import Definitions.Def_FourMsgQMA_BaseProtocol

namespace FourMsgQMA

open QAlgorithms.Complexity

/-- **The base protocol from LWE** (§3.4, p.14, PDF 16, and §4.1, p.26, PDF 28): "The ordinary-key
CM–FHM construction, specialized to one instance, realizes the amplified input-independent batch
interface under its LWE assumption [BKL+22, Theorem 10.4]." Goyal, Koppula, STOC 2027 submission
(sha256 6c523d45…), pinned-down version (operator request).

For every `ε ∈ (0, 1)`, under `Hyp(ε)`, every QMA promise problem `L` with verification family `F`
has a four-message base protocol with input-independent setup `Gen(1^λ, T)`, a uniform challenge,
sizes polynomial in `(λ, T)`, overwhelming statistical completeness for `N(λ, T)` copies of any
witness in `W_Q(x, 2/3)`, and negligible soundness (Definition 3.7 with `s₀ = 0`).

**Formalization Note** `T = t_L(x)`; the challenge is the verifier's second message, uniform in
`{0,1}^{m(λ,T)}`; "its LWE assumption" is read as `Hyp(ε)`. -/
theorem base_protocol_bkl22 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hLWE : LWEHyp ε)
    (L : PromiseProblem) (F : QMAFamily) (hLF : IsQMAVerifierFor L F) :
    ∃ B : BaseProtocol, B.IsUniform ∧ B.Bounded F ∧ B.Complete L F ∧ B.Sound L F := by sorry

end FourMsgQMA
