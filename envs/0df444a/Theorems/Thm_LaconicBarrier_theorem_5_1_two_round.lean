-- Prove2me | Theorems.Thm_LaconicBarrier_theorem_5_1_two_round
-- name    : LaconicBarrier.theorem_5_1_two_round
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:56.138015+00:00
-- url     : https://prove2.me/theorems/cd637d00-c95c-4c41-9a8c-86897d999bf2
-- title:
--   Proof of Theorem 5.1 — a two-round proof for the complement with gap $\Omega(\Delta^2/(\ell_P+\log(1/\Delta)))$
-- statement:
--   Assume the hypotheses of Theorem 5.1: $T \ge n$ and $\ell_P \ge 1$ time-constructible, efficiently computable $\epsilon_c, \epsilon_s \in [0,1]$ with $\Delta = 1 - \epsilon_c - \epsilon_s > 0$, and
--   $$
--   (L_{\mathrm{yes}}, L_{\mathrm{no}}) \in \mathsf{IP}(\text{rounds} = 1, \text{verifier time} = T, \text{prover comm} = \ell_P, \text{completeness} \ge 1-\epsilon_c, \text{soundness} \le \epsilon_s).
--   $$
--   Then the complement has a two-round interactive proof,
--   $$
--   (L_{\mathrm{no}}, L_{\mathrm{yes}}) \in \mathsf{IP}\bigl(\text{rounds} = 2,\ \text{verifier time} = 2^{\ell_P}\mathrm{poly}(T + \ell_P + 1/\Delta),\ \text{prover comm, verifier comm, verifier randomness} = \mathrm{poly}(T + \ell_P + 1/\Delta),\ \text{completeness} \ge 1-\epsilon'_c,\ \text{soundness} \le \epsilon'_s\bigr),
--   $$
--   where
--   $$
--   1 - \epsilon'_c - \epsilon'_s \ge \Omega\!\left(\frac{\Delta^2}{\ell_P + \log(1/\Delta)}\right).
--   $$
--
--   This protocol (bucket hashing of the verifier's random tapes, with the prover certifying bucket contents) is the core of the complementation step; amplification, the private-to-public-coin transformation and round collapse then give Theorem 5.1.
--
--   Differences from the source:
--   - reading: Ω(Δ²/(ℓ_P + log(1/Δ))) → c₀·Δ²/(ℓ_P + ln(1/Δ)) for an absolute constant c₀ > 0 chosen before the problem; natural logarithm; reason: the Θ-parameters of the protocol (display (1)) are absolute constants; a change of base changes c₀ only
--   - reading: 'there exist completeness and soundness error bounds' (standing assumption: error bounds efficiently computable) → the error bounds produced lie in [0, 1] and are efficiently computable; reason: the standing assumption applies to the error bounds the theorem produces; the next step (Theorem 5.1) needs them
--   - generalization: a language L, or promise problems (L_yes, L_no), with bounds functions of n = |x| → promise problems on any input type with an encoding, bounds functions of the input; T(n) ≥ n read as T ≥ the length of the encoded input; reason: the language case is (L, L̄) on strings with bounds depending on |x|
--   - reading: standing assumptions (p.15): resource bounds time-constructible, baselines and error bounds efficiently computable, 'we do not repeat these conditions' → explicit hypotheses TimeConstr / EffComputable / EffReal on the bounds and constants the statement uses; reason: the paper's own convention; without them a uniform verifier cannot compute its thresholds
--   - encoding: verifier communication and randomness omitted (default O(T)) → verifier communication and randomness C·(T+1) for some constant C; reason: the paper's default (p.25)
--   - encoding: IP / AM classes with verifier time O(T) and communication bounds 'for every prover strategy' → verifier time per verifier step (computed from the transcript) at most C·(T+1); deterministic provers; transcripts over the prover budget rejected; reason: for at most two rounds the per-step and total times agree up to a constant; the best coins of a randomized prover do as well
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), proof of Theorem 5.1, p.30 (PDF p.33)

import Mathlib
import Definitions.Def_LaconicBarrier_InIP
import Definitions.Def_LaconicBarrier_TimeConstr
import Definitions.Def_LaconicBarrier_EffComputable

namespace LaconicBarrier

/-- **The two-round protocol in the proof of Theorem 5.1** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), proof of Theorem 5.1, p.30): under
the hypotheses of Theorem 5.1, the complement has a two-round (private-coin) interactive proof,
`(L_no, L_yes) ∈ IP(rounds = 2, verifier time = 2^{ℓ_P} poly(T + ℓ_P + 1/∆), prover comm, verifier
comm, verifier randomness = poly(T + ℓ_P + 1/∆), completeness ≥ 1 − ϵ′_c, soundness ≤ ϵ′_s)`, with
`1 − ϵ′_c − ϵ′_s ≥ Ω(∆²/(ℓ_P + log(1/∆)))`.

**Formalization Note** The constant of `Ω` is absolute (chosen before the problem); the new error
bounds lie in `[0, 1]` and are efficiently computable, as the standing assumptions (§4.1.1, p.15)
require of error bounds. `log` is the natural logarithm (a change of base changes the constant). -/
theorem theorem_5_1_two_round : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {I : Type} (enc : I → List (List Bool)) (yes no : Set I) (T ℓP : I → ℕ) (εc εs : I → ℝ),
    (∀ i, (KarpLiptonOM.tupleEnc (enc i)).length ≤ T i) → (∀ i, 1 ≤ ℓP i) →
    (∀ i, εc i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, εs i ∈ Set.Icc (0 : ℝ) 1) →
    (∀ i, 0 < 1 - εc i - εs i) → TimeConstr enc T → TimeConstr enc ℓP →
    EffComputable enc εc (fun i => T i + ℓP i + ⌈1 / (1 - εc i - εs i)⌉₊) →
    EffComputable enc εs (fun i => T i + ℓP i + ⌈1 / (1 - εc i - εs i)⌉₊) →
    (∃ C : ℕ, InIP enc yes no 1 T ℓP (fun i => C * (T i + 1)) (fun i => C * (T i + 1)) εc εs) →
    ∃ (d : ℕ) (εc' εs' : I → ℝ),
      (∀ i, εc' i ∈ Set.Icc (0 : ℝ) 1 ∧ εs' i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, c₀ * (1 - εc i - εs i) ^ 2 / ((ℓP i : ℝ) + Real.log (1 / (1 - εc i - εs i))) ≤
        1 - εc' i - εs' i) ∧
      EffComputable enc εc' (fun i => T i + ℓP i + ⌈1 / (1 - εc i - εs i)⌉₊) ∧
      EffComputable enc εs' (fun i => T i + ℓP i + ⌈1 / (1 - εc i - εs i)⌉₊) ∧
      InIP enc no yes 2
        (fun i => 2 ^ ℓP i * ⌈((T i + ℓP i : ℕ) + 1 / (1 - εc i - εs i) + 2 : ℝ) ^ d⌉₊)
        (fun i => ⌈((T i + ℓP i : ℕ) + 1 / (1 - εc i - εs i) + 2 : ℝ) ^ d⌉₊)
        (fun i => ⌈((T i + ℓP i : ℕ) + 1 / (1 - εc i - εs i) + 2 : ℝ) ^ d⌉₊)
        (fun i => ⌈((T i + ℓP i : ℕ) + 1 / (1 - εc i - εs i) + 2 : ℝ) ^ d⌉₊)
        εc' εs' := by sorry

end LaconicBarrier
