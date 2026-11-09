-- Prove2me | Theorems.Thm_KnapsackFPRAS_theorem_1_1
-- name    : KnapsackFPRAS.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:39:53.262262+00:00
-- url     : https://prove2.me/theorems/a3d10592-8285-4f12-a716-2fc938da85f6
-- title:
--   Theorem 1.1 — an FPRAS for counting knapsack in $\tilde O(n/\varepsilon^2)$ word-RAM time
-- statement:
--   There is a randomized algorithm that, given nonnegative integers $w_1,\dots,w_n$, a nonnegative integer $T$ and a real $0<\varepsilon<1$, returns a number $\hat F$ with
--
--   $$
--   \Pr\bigl[(1-\varepsilon)|\Omega|\le\hat F\le(1+\varepsilon)|\Omega|\bigr]\ge\frac23,
--   $$
--
--   where $\Omega=\{X\subseteq[n]: w(X)\le T\}$, in $\tilde O(n/\varepsilon^2)$ time on a word RAM with $O(\log(n/\varepsilon)+\log T)$-bit words.
--
--   Precisely: there are a program $P$ of the randomized word RAM and constants $c,C,k$ such that for every $n$, every $w\in\mathbb N^n$, every $T\in\mathbb N$ and every real $0<\varepsilon<1$, with $K=\lceil1/\varepsilon\rceil$, words of $W=c(\lfloor\log_2(n+1)\rfloor+\lfloor\log_2K\rfloor+\lfloor\log_2(T+1)\rfloor+1)$ bits and
--
--   $$
--   N=\Bigl\lceil C\,\frac{n+1}{\varepsilon^2}\Bigl(1+\log_2\frac{n+1}{\varepsilon}\Bigr)^k\Bigr\rceil ,
--   $$
--
--   on the input $(n,T,K,\min(w_1,T+1),\dots,\min(w_n,T+1))$:
--
--   1. every run of $P$ halts within $N$ steps, whatever its random words;
--   2. for at least $2/3$ of the $2^{WN}$ equally likely values of the first $N$ random words, the output $\hat F=m\cdot2^e$ (mantissa $m$, signed exponent $e$) satisfies $(1-\varepsilon)|\Omega|\le\hat F\le(1+\varepsilon)|\Omega|$.
--
--   Exact counting of knapsack solutions is #P-complete. The bound improves the $\tilde O(n^{3/2}/\varepsilon^2)$ FPRAS of Feng and Jin and answers their question whether time $\tilde O(n/\mathrm{poly}(\varepsilon))$ is possible.
--
--   Differences from the source:
--   - reading: the word RAM model (no instruction set given) → the machine KnapsackFPRAS.Machine: unsigned W-bit words with +, −, ×, ÷, mod, bitwise operations, shifts, indirect load/store, a branch, halt, and one uniform W-bit random word per rand, each at unit cost; reason: the paper fixes no instruction set; this is the standard unit-cost randomized word RAM, with no unit-cost real, floating-point or exponential operation
--   - reading: O(log(n/ε) + log T)-bit words → W = c(⌊log₂(n+1)⌋ + ⌊log₂⌈1/ε⌉⌋ + ⌊log₂(T+1)⌋ + 1), c chosen before the instance; reason: one fixed coefficient for the O(·); the +1's cover n = 0 and T = 0
--   - generalization: the algorithm is given ε → the machine is given only K = ⌈1/ε⌉ and must meet the (1 ± ε) guarantee for the real ε; reason: the program knows less; a program for this input also serves an exactly given ε, for every real ε in (0, 1)
--   - encoding: the weights w₁, …, w_n → min(wᵢ, T + 1); reason: an item heavier than T is in no feasible set, so Ω is unchanged; capped weights fit in O(log T)-bit words
--   - encoding: given n, w, T, ε; returns a number F̂ → input layout n, T, K, weights in cells 0, 1, 2, 3…; output F̂ = [0]·2^{[1]} with a signed exponent; reason: |Ω| ≤ 2ⁿ needs a floating representation; the paper's numbers are O(κ)-bit floats
--   - encoding: Õ(n/ε²) time → every run halts within ⌈C((n+1)/ε²)(1 + log₂((n+1)/ε))^k⌉ steps; reason: Õ(g) = O(g polylog(n/ε)) for n ≥ 2 (§2); n + 1 covers n ≤ 1; worst case by the cutoff of footnote 6, p.54
--   - encoding: probability at least 2/3 → at least 2/3 of the 2^{WN} values of the first N random words; reason: a run of at most N steps reads at most N uniform words, so this fraction is the probability
--   - encoding: [n] → Fin n; reason: index shift; same instances
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Theorem 1.1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_KnapsackFPRAS_feasible
import Definitions.Def_KnapsackFPRAS_Machine

set_option autoImplicit false

namespace KnapsackFPRAS

/-- **Theorem 1.1**, p.1. "There is a randomized algorithm that, given nonnegative integers
𝑤1, …, 𝑤𝑛, 𝑇, and 0 < 𝜀 < 1, with Ω defined in Eq. (1), returns a number F̂ satisfying
Pr[(1 − 𝜀)|Ω| ≤ F̂ ≤ (1 + 𝜀)|Ω|] ≥ 2/3 in Õ(𝑛/𝜀²) time in the word RAM model with
O(log(𝑛/𝜀) + log 𝑇)-bit words."

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Theorem 1.1, p.1 (PDF p.2).

**Formalization Note.** One program `P` and constants `c, C, k` are chosen before the instance.
For every `n`, every `w : Fin n → ℕ` (zero weights and weights above `T` allowed), every
`T : ℕ` and every real `0 < ε < 1`: words have `W = c(⌊log₂(n+1)⌋ + ⌊log₂ K⌋ + ⌊log₂(T+1)⌋ + 1)`
bits with `K = ⌈1/ε⌉`; the machine starts on `(n, T, K, min(w₀, T+1), …, min(w_{n−1}, T+1))`;
every run (every random tape) halts within `N = ⌈C ((n+1)/ε²)(1 + log₂((n+1)/ε))^k⌉` steps;
and for at least `2/3` of the `2^{W N}` values of the first `N` random words (the only words
a run of at most `N` steps reads) the output `F̂ = [0]·2^{[1]}` (signed exponent) satisfies
`(1 − ε)|Ω| ≤ F̂ ≤ (1 + ε)|Ω|`. Õ(g) is `C·g·(1 + log₂((n+1)/ε))^k` with `n + 1` in place of
`n` so that `n ≤ 1` is covered. -/
theorem theorem_1_1 :
    ∃ P : List Machine.Instr, ∃ c C k : ℕ,
      ∀ (n : ℕ) (w : Fin n → ℕ) (T : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
        let K := ⌈1 / ε⌉₊
        let W := Machine.wordLen c n K T
        let N := ⌈(C : ℝ) * (((n : ℝ) + 1) / ε ^ 2) * (1 + Real.logb 2 (((n : ℝ) + 1) / ε)) ^ k⌉₊
        let x := Machine.input W n T K (fun i => min (w i) (T + 1)) []
        (∀ ρ : ℕ → BitVec W, (Machine.exec P ρ N 0 0 x).isSome) ∧
        2 * 2 ^ (W * N) ≤ 3 * Machine.count (fun s => ∃ m,
          Machine.exec P (Machine.tape W s) N 0 0 x = some m ∧
          (1 - ε) * ((feasible w T).card : ℝ) ≤ Machine.outReal m ∧
          Machine.outReal m ≤ (1 + ε) * ((feasible w T).card : ℝ)) (2 ^ (W * N)) := by sorry

end KnapsackFPRAS
