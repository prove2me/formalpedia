-- Prove2me | Theorems.Thm_OptQJunta_lemma_4_5
-- name    : OptQJunta.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:34.304276+00:00
-- url     : https://prove2.me/theorems/b503eefc-1677-4a11-891f-10c1387f998b
-- title:
--   Lemma 4.5 — partial support recovery with $\lceil C_{\mathrm{rec}}(\tau^{-1/2}+k^2\ln(ek))\rceil$ queries
-- statement:
--   Fix integers $1\le k\le n$ and $0<\tau\le1$, and let $H_\tau=\lceil2\log_{2,+}(\tau2^k)\rceil$. There is an absolute constant $C_{\mathrm{rec}}>0$ and, for all such $k,n,\tau$, a quantum query algorithm that uses at most $\lceil C_{\mathrm{rec}}(\tau^{-1/2}+k^2\ln(ek))\rceil$ queries on every input and, for every Boolean function $f:\{0,1\}^n\to\{0,1\}$ with $K=\mathrm{supp}(f)$:
--
--   1. it returns either a set $J\subseteq[n]$ with $|J|\le k$ or Overfull;
--   2. if $|K|\le k$, it never returns Overfull and always has $J\subseteq K$;
--   3. if $|K|\le k$, then with probability at least $19/20$ its output also satisfies
--
--   $$
--   \nu_J<\tau\quad\text{or}\quad|K\setminus J|\le H_\tau .
--   $$
--
--   The source states this for its procedure $\mathrm{PartialRecover}(f;k,\tau)$ (p.56); here it is the existence of an algorithm with these guarantees, which is how Theorem 4.2 uses it. It handles exponentially small $\varepsilon$ in Theorem 4.2.
--
--   Differences from the source:
--   - reading: the guarantees of the named procedure $\mathrm{PartialRecover}(f;k,\tau)$ described on p.56 → there exists a query algorithm with the same query bound and the same three output guarantees; reason: the procedure is specified in prose (exact conditional sampling with expected-time searches and a global cap) and is not written as a Lean term; the existence statement is exactly what the proof of Theorem 4.2 uses, and the procedure is a witness
--   - encoding: a tester with ancillas, private randomness, intermediate measurements and adaptivity, whose query count is the largest over all inputs and executions (§2.5, p.22) → a `QAlgorithms.QueryAlg`: an oracle-independent unit start state, exactly $T$ standard queries $|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$ interleaved with oracle-independent unitaries on an arbitrary finite workspace, and an output read from the final computational-basis measurement; reason: deferred measurement, purification of the private randomness and padding of shorter executions turn every tester of the source into one of this form with the same output law on every input, and conversely
--   - encoding: "returns either …", "never returns Overfull and always has $J\subseteq K$" on every execution → the complementary outputs have probability $0$; reason: deferred measurement: an output event never occurs on any execution exactly when its probability is $0$
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Lemma 4.5, p.56

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OptQJunta_infl
import Definitions.Def_OptQJunta_nuJ
import Definitions.Def_OptQJunta_TestsJunta

open QAlgorithms

namespace OptQJunta

/-- **Lemma 4.5** (Partial support recovery; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.56). Fix integers `1 ≤ k ≤ n` and `0 < τ ≤ 1`.
For every Boolean function `f : {0,1}^n → {0,1}`, `PartialRecover(f; k, τ)` uses at most
`⌈C_rec(τ^{−1/2} + k² ln(ek))⌉` queries on every input, for a sufficiently large absolute constant
`C_rec`. It returns either a set `J ⊆ [n]` with `|J| ≤ k` or Overfull. If `K = supp(f)` satisfies
`|K| ≤ k`, the procedure never returns Overfull and always has `J ⊆ K`. With probability at least
`19/20`, its output also satisfies either `ν_J < τ` or `|K ∖ J| ≤ H_τ`, where
`H_τ = ⌈2 log₂,₊(τ2^k)⌉`.

**Formalization Note** Reading: the lemma is stated for the procedure that it names. Here it is the
statement that some query algorithm (a `QAlgorithms.QueryAlg` in unitary form, standard queries)
with the same query bound has the same output guarantees, which is what the proof of Theorem 4.2
uses. The output is `none` (Overfull) or `some J`. "Returns either …" and "never returns Overfull
and always has `J ⊆ K`" are probability-`0` statements for the complementary outputs (the first on
every `f`, the second under `|K| ≤ k`). `ln` is natural, `log₂,₊ x = max{0, log₂ x}`. -/
theorem lemma_4_5 :
    ∃ Crec : ℝ, 0 < Crec ∧ ∀ k n : ℕ, 1 ≤ k → k ≤ n → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (T : ℕ)
        (A : QueryAlg (Qubits n) Bool W T)
        (out : (Qubits n × Bool) × W → Option (Finset (Fin n))),
        T ≤ ⌈Crec * (τ ^ (-(1 : ℝ) / 2) + (k : ℝ) ^ 2 * Real.log (Real.exp 1 * k))⌉₊ ∧
        ∀ f : Qubits n → Bool,
          outEventProb A (xorOracle f) out (fun o => ∃ J, o = some J ∧ k < J.card) = 0 ∧
          ((supp f).card ≤ k →
            outEventProb A (xorOracle f) out (fun o => o = none) = 0 ∧
            outEventProb A (xorOracle f) out (fun o => ∃ J, o = some J ∧ ¬ J ⊆ supp f) = 0 ∧
            19 / 20 ≤ outEventProb A (xorOracle f) out (fun o => ∃ J, o = some J ∧
              (nuJ f J < τ ∨ (supp f \ J).card ≤ ⌈2 * log2p (τ * 2 ^ k)⌉₊))) := by sorry

end OptQJunta
