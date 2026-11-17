-- Prove2me | Theorems.Thm_LaconicBarrier_Supplement_theorem_5_2
-- name    : LaconicBarrier.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:34:19.827484+00:00
-- url     : https://prove2.me/theorems/d9b589e1-6aa7-474c-8e9c-9560db0f0e36
-- title:
--   Theorem 5.2 — one-round proofs with an instance-independent first message give $\mathsf{SIZE}[2^{\ell_P}\mathrm{poly}(T+\ell_P+1/\Delta)]$
-- statement:
--   Suppose $L$ has a one-round interactive proof with verifier time $T(n) \ge n$, prover-message length $\ell_P(n) \ge 1$, and error bounds $\epsilon_c(n), \epsilon_s(n) \in [0,1]$ with
--   $$
--   \Delta(n) = 1 - \epsilon_c(n) - \epsilon_s(n) > 0 .
--   $$
--   Assume the first-message map depends on $x$ only through its length: $V_1(x; \rho) = V_1(1^n; \rho)$ for every $x \in \{0,1\}^n$ and every random tape $\rho$. Then
--   $$
--   L \in \mathsf{SIZE}\Bigl[2^{\ell_P(n)}\,\mathrm{poly}\bigl(T(n) + \ell_P(n) + 1/\Delta(n)\bigr)\Bigr].
--   $$
--   Moreover, $L$ can be decided deterministically within this time using advice of length $\mathrm{poly}(T + \ell_P + 1/\Delta)$ that depends only on $n$.
--
--   The standing assumptions of the paper apply: $T$ and $\ell_P$ are time-constructible, and $\epsilon_c, \epsilon_s$ are efficiently computable.
--
--   A first message independent of the instance can be sampled once per length and placed in the advice, so a one-round proof of this kind turns into a non-uniform algorithm whose cost is exponential only in the prover's message length. Corollary 6.9 applies this to adaptive SNARGs.
--
--   **Formalization Note** The proof system is the mission's `IPVerifier.Proves` with one round on inputs $x$. Verifier communication and randomness take the paper's default $O(T)$. "Depends on $x$ only through its length" includes the number of coins, so the tape $\rho$ is used on both sides. $\mathrm{poly}(T + \ell_P + 1/\Delta)$ is $(T + \ell_P + \lceil 1/\Delta\rceil + 2)^d$ with one $d$ for all $n$. The deterministic algorithm is one machine of the mission's model on input $(x, a(|x|))$.
--
--   Differences from the source:
--   - encoding: a one-round interactive proof for L with verifier time T, prover-message length ℓ_P, errors ϵ_c, ϵ_s (verifier communication and randomness omitted) → IPVerifier.Proves on inputs x with one round, verifier communication and randomness C·(T(n)+1) for some constant C; reason: the paper's default for omitted bounds is O(T(n)) (p.25, p.28: 'As for IP … omitted communication and randomness bounds to O(T(n))')
--   - encoding: V_1(x; ρ) = V_1(1^n; ρ) for every x ∈ {0,1}^n and random tape ρ → V.coins x = V.coins (1^{|x|}) and msg x ρ [] = msg (1^{|x|}) ρ [] with ρ transported along that equality; reason: the same random tape on both sides requires the same number of coins
--   - encoding: L ∈ SIZE[2^{ℓ_P(n)} poly(T(n) + ℓ_P(n) + 1/∆(n))] → ∃ d, ∀ n, a circuit with at most 2^{ℓ_P(n)}·(T(n) + ℓ_P(n) + ⌈1/∆(n)⌉ + 2)^d gates decides L on {0,1}^n; reason: one polynomial for all n; ⌈1/∆⌉ and 1/∆ differ by less than 1
--   - reading: L can be decided deterministically in this time with advice of length poly(T + ℓ_P + 1/∆) depending only on n → one machine M of the mission's model and advice a(n) with |a(n)| ≤ (T + ℓ_P + ⌈1/∆⌉ + 2)^d such that M on (x, a(|x|)) halts within 2^{ℓ_P}·(…)^d steps with output 1 iff x ∈ L; reason: the mission's single machine model (paper.md decision 4); 'this time' is the bound of the SIZE clause
--   - reading: standing assumptions (p.15): resource bounds time-constructible, baselines and error bounds efficiently computable, 'we do not repeat these conditions' → explicit hypotheses TimeConstr / EffComputable / EffReal on the bounds and constants the statement uses; reason: the paper's own convention, applied as in the published theorem_6_3
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 5.2, pp.35–36 (PDF 38–39)

import Mathlib
import Definitions.Def_LaconicBarrier_InIP
import Definitions.Def_LaconicBarrier_TimeConstr
import Definitions.Def_LaconicBarrier_EffComputable
import Definitions.Def_LaconicBarrier_Supplement_SizeAtMost

namespace LaconicBarrier.Supplement

open KarpLiptonOM

open Classical in
/-- **Theorem 5.2** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for
Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Theorem 5.2,
pp.35–36): one-round proofs with an instance-independent first message give small circuits. Suppose
`L` has a one-round interactive proof with verifier time `T(n) ≥ n`, prover-message length
`ℓ_P(n) ≥ 1` and error bounds `ϵ_c(n), ϵ_s(n) ∈ [0, 1]` with `∆(n) = 1 − ϵ_c(n) − ϵ_s(n) > 0`, whose
first-message map depends on `x` only through its length: `V₁(x; ρ) = V₁(1ⁿ; ρ)` for every
`x ∈ {0,1}ⁿ` and random tape `ρ`. Then `L ∈ SIZE[2^{ℓ_P(n)} poly(T(n) + ℓ_P(n) + 1/∆(n))]`, and `L`
can be decided deterministically in this time with advice of length `poly(T + ℓ_P + 1/∆)` depending
only on `n`.

**Formalization Note** The proof system is the published `IPVerifier.Proves` with one round on
inputs `x` (encoded as the one-component tuple `x`), verifier communication and randomness the
default `O(T)` (§4.2.1, p.25: omitted bounds default to `O(T(n))`); its first message is `msg x ρ []`.
"Depends on `x` only through its length" includes the number of coins: `V.coins x = V.coins (1^{|x|})`,
and the tape `ρ` is transported along that equality. `poly(T + ℓ_P + 1/∆)` is `(T + ℓ_P + ⌈1/∆⌉ + 2)^d`
for one `d` for all `n`. The deterministic algorithm is a machine of the mission's model on input
`(x, a(|x|))` that outputs `1` iff `x ∈ L`. The standing assumptions (§4.1.1, p.15) are hypotheses:
`T`, `ℓ_P` time-constructible, `ϵ_c`, `ϵ_s` efficiently computable. -/
theorem theorem_5_2 (L : Set (List Bool)) (T ℓP : ℕ → ℕ) (εc εs : ℕ → ℝ)
    (hT : ∀ n, n ≤ T n) (hℓP : ∀ n, 1 ≤ ℓP n) (hεc : ∀ n, εc n ∈ Set.Icc (0 : ℝ) 1)
    (hεs : ∀ n, εs n ∈ Set.Icc (0 : ℝ) 1) (hΔ : ∀ n, 0 < 1 - εc n - εs n)
    (hTc : TimeConstr (fun n => [unary n]) T) (hℓc : TimeConstr (fun n => [unary n]) ℓP)
    (hεcc : EffComputable (fun n => [unary n]) εc
      (fun n => T n + ℓP n + ⌈1 / (1 - εc n - εs n)⌉₊))
    (hεsc : EffComputable (fun n => [unary n]) εs
      (fun n => T n + ℓP n + ⌈1 / (1 - εc n - εs n)⌉₊))
    (hIP : ∃ (C : ℕ) (V : IPVerifier (List Bool)),
      V.Proves (fun x => [x]) L Lᶜ 1 (fun x => T x.length) (fun x => ℓP x.length)
        (fun x => C * (T x.length + 1)) (fun x => C * (T x.length + 1))
        (fun x => εc x.length) (fun x => εs x.length) ∧
      ∃ hc : ∀ x : List Bool, V.coins x = V.coins (unary x.length),
        ∀ (x : List Bool) (ρ : Fin (V.coins x) → Bool),
          V.msg x ρ [] = V.msg (unary x.length) (fun t => ρ (Fin.cast (hc x).symm t)) []) :
    ∃ d : ℕ,
      InSIZE L (fun n => 2 ^ ℓP n * (T n + ℓP n + ⌈1 / (1 - εc n - εs n)⌉₊ + 2) ^ d) ∧
      ∃ (M : OracleTM) (a : ℕ → List Bool), ∀ n : ℕ,
        (a n).length ≤ (T n + ℓP n + ⌈1 / (1 - εc n - εs n)⌉₊ + 2) ^ d ∧
        ∀ x : List Bool, x.length = n →
          RunsWithin M [x, a n] [decide (x ∈ L)]
            (2 ^ ℓP n * (T n + ℓP n + ⌈1 / (1 - εc n - εs n)⌉₊ + 2) ^ d) := by sorry

end LaconicBarrier.Supplement
