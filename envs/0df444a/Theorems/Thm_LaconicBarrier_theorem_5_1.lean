-- Prove2me | Theorems.Thm_LaconicBarrier_theorem_5_1
-- name    : LaconicBarrier.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:07.103867+00:00
-- url     : https://prove2.me/theorems/66bac160-a0ef-410f-9d4f-127d2afd4d67
-- title:
--   Theorem 5.1 — one-round laconic proofs give $\mathsf{coAM}$ with polynomial communication
-- statement:
--   Let $T(n) \ge n$ and $\ell_P(n) \ge 1$ be bounds and let $\epsilon_c(n), \epsilon_s(n) \in [0,1]$ be error bounds with $\Delta(n) = 1 - \epsilon_c(n) - \epsilon_s(n) > 0$. If
--   $$
--   L \in \mathsf{IP}(\text{rounds} = 1, \text{verifier time} = T, \text{prover comm} = \ell_P, \text{completeness} \ge 1-\epsilon_c, \text{soundness} \le \epsilon_s),
--   $$
--   then
--   $$
--   L \in \mathsf{coAM}\bigl(\text{rounds} = 1,\ \text{verifier time} = 2^{\ell_P}\mathrm{poly}(T + \ell_P + 1/\Delta),\ \text{prover comm, verifier comm, verifier randomness} = \mathrm{poly}(T + \ell_P + 1/\Delta)\bigr),
--   $$
--   and the public-coin proof for $\overline L$ has completeness at least $2/3$ and soundness at most $1/3$. The same holds for promise problems $(L_{\mathrm{yes}}, L_{\mathrm{no}})$, with the public-coin proof deciding $(L_{\mathrm{no}}, L_{\mathrm{yes}})$.
--
--   The exponential cost is in the prover's message length $\ell_P$ only, not in the verifier's message: this is what lets a one-bit argument with a long first message be complemented in polynomial time.
--
--   Differences from the source:
--   - generalization: a language L, or promise problems (L_yes, L_no), with bounds functions of n = |x| → promise problems on any input type with an encoding, bounds functions of the input; T(n) ≥ n read as T ≥ the length of the encoded input; reason: the language case is (L, L̄) on strings with bounds depending on |x|
--   - reading: standing assumptions (p.15): resource bounds time-constructible, baselines and error bounds efficiently computable, 'we do not repeat these conditions' → explicit hypotheses TimeConstr / EffComputable / EffReal on the bounds and constants the statement uses; reason: the paper's own convention; without them a uniform verifier cannot compute its thresholds
--   - encoding: verifier communication and randomness omitted (default O(T)) → verifier communication and randomness C·(T+1) for some constant C; reason: the paper's default (p.25)
--   - encoding: IP / AM classes with verifier time O(T) and communication bounds 'for every prover strategy' → verifier time per verifier step (computed from the transcript) at most C·(T+1); deterministic provers; transcripts over the prover budget rejected; reason: for at most two rounds the per-step and total times agree up to a constant; the best coins of a randomized prover do as well
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 5.1, p.30 (PDF p.33)

import Mathlib
import Definitions.Def_LaconicBarrier_InIP
import Definitions.Def_LaconicBarrier_TimeConstr
import Definitions.Def_LaconicBarrier_EffComputable

namespace LaconicBarrier

/-- **Theorem 5.1** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 5.1, p.30), for promise problems. Let `T ≥ n` and `ℓ_P ≥ 1` be
time-constructible bounds and `ϵ_c, ϵ_s ∈ [0, 1]` efficiently computable error bounds with
`∆ = 1 − ϵ_c − ϵ_s > 0`. If `(L_yes, L_no) ∈ IP(rounds = 1, verifier time = T, prover comm = ℓ_P,
completeness ≥ 1 − ϵ_c, soundness ≤ ϵ_s)` (verifier communication and randomness `O(T)`, the
default), then `(L_no, L_yes)` has a one-round public-coin proof with verifier time
`2^{ℓ_P} · poly(T + ℓ_P + 1/∆)`, prover and verifier communication and verifier randomness
`poly(T + ℓ_P + 1/∆)`, completeness at least `2/3` and soundness at most `1/3`: for a language `L`,
`L ∈ coAM(…)`.

**Formalization Note** Bounds are functions of the common input; `n` is the length of its encoding.
"Efficiently computable" error bounds are approximable to `1/(N+1)` in time polynomial in
`T + ℓ_P + ⌈1/∆⌉ + N` (§4.1.1, p.15, standing assumptions). -/
theorem theorem_5_1 {I : Type} (enc : I → List (List Bool)) (yes no : Set I) (T ℓP : I → ℕ)
    (εc εs : I → ℝ) (hT : ∀ i, (KarpLiptonOM.tupleEnc (enc i)).length ≤ T i)
    (hℓP : ∀ i, 1 ≤ ℓP i) (hεc : ∀ i, εc i ∈ Set.Icc (0 : ℝ) 1)
    (hεs : ∀ i, εs i ∈ Set.Icc (0 : ℝ) 1) (hΔ : ∀ i, 0 < 1 - εc i - εs i)
    (hTc : TimeConstr enc T) (hℓc : TimeConstr enc ℓP)
    (hεcc : EffComputable enc εc (fun i => T i + ℓP i + ⌈1 / (1 - εc i - εs i)⌉₊))
    (hεsc : EffComputable enc εs (fun i => T i + ℓP i + ⌈1 / (1 - εc i - εs i)⌉₊))
    (hIP : ∃ C : ℕ, InIP enc yes no 1 T ℓP (fun i => C * (T i + 1)) (fun i => C * (T i + 1))
      εc εs) :
    ∃ d : ℕ, InAM enc no yes 1
      (fun i => 2 ^ ℓP i * ⌈((T i + ℓP i : ℕ) + 1 / (1 - εc i - εs i) + 2 : ℝ) ^ d⌉₊)
      (fun i => ⌈((T i + ℓP i : ℕ) + 1 / (1 - εc i - εs i) + 2 : ℝ) ^ d⌉₊)
      (fun i => ⌈((T i + ℓP i : ℕ) + 1 / (1 - εc i - εs i) + 2 : ℝ) ^ d⌉₊)
      (fun i => ⌈((T i + ℓP i : ℕ) + 1 / (1 - εc i - εs i) + 2 : ℝ) ^ d⌉₊)
      (fun _ => 1 / 3) (fun _ => 1 / 3) := by sorry

end LaconicBarrier
