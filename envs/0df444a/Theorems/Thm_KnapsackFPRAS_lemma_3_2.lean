-- Prove2me | Theorems.Thm_KnapsackFPRAS_lemma_3_2
-- name    : KnapsackFPRAS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:35:51.107328+00:00
-- url     : https://prove2.me/theorems/7a355495-9928-4895-adf4-9c3d37cfd09f
-- title:
--   Lemma 3.2 — the tilt $\lambda^*$: $|\Omega|\le C^{\lambda^*}_w\le16n|\Omega|$, $\mathbb E\,w(X)\le2T$, $\lambda^*T\le8\ell\kappa$, in $\tilde O(n)$ time
-- statement:
--   Assume $1\le w_i\le T$ for all $i$ and $\sum_i w_i>T$ (the standing assumption (7)), let $0<\varepsilon<1$ and $\kappa=\lceil\log_2(100n/\varepsilon)\rceil$, and let $\ell$ be a power of two with $2\le\ell<8n$ and $\sum_{i:w_i\le T/\ell}w_i<T/2$ (the output of Lemma 2.4).
--
--   There are a program $P$ of the randomized word RAM and constants $c,c',C,k$ such that, on the input $(n,T,\lceil1/\varepsilon\rceil,w_1,\dots,w_n,\ell)$ with the word length of Theorem 1.1, every run halts within $Cn\kappa^k$ steps and outputs a mantissa $m<2^{c'\kappa}$ and an exponent $j\le c'\kappa$ such that $y^*=m/2^j$ and $\lambda^*=y^*/T$ satisfy
--
--   $$
--   |\Omega|\le C^{\lambda^*}_w\le16n|\Omega|,\qquad \mathbb E_{X\sim Q^{\lambda^*}_w}[w(X)]\le2T,\qquad \lambda^*T\le8\ell\kappa .
--   $$
--
--   This is the tilt used by the whole algorithm: the first bound converts tilted probability into counts, the second bounds the expected size of each weight class (Corollary 3.4), and the third controls the rounding parameters of Section 4.
--
--   Differences from the source:
--   - reading: the lemma as printed in §3 → hypotheses 1 ≤ wᵢ ≤ T and T < ∑ wᵢ; reason: standing assumption (7) of §2 (p.9)
--   - generalization: ℓ is the parameter returned by Lemma 2.4 → any power of two ℓ with 2 ≤ ℓ < 8n satisfying (9), given in cell n + 3; reason: the proof uses only these properties of ℓ; the ℓ of Lemma 2.4 is one such
--   - reading: an Õ(n)-time algorithm → one program P of the machine of Theorem 1.1, chosen with its constants before the instance, every run of which halts within C·n·κ^k steps and outputs a valid λ*; reason: the paper's model is that of Theorem 1.1; the proof of Theorem 1.1 budgets no failure probability for this step
--   - reading: using O(log(n/ε)) bits of numerical precision → the machine's words of Theorem 1.1, O(log(n/ε) + log T) bits; reason: numerical precision has no meaning on the machine beyond its word length; the words must hold the input T
--   - reading: y* is a number with O(log(n/ε)) bits → y* = m/2^j with m < 2^{c'κ} and j ≤ c'κ, c' chosen before the instance; reason: a binary fraction of O(κ) bits
--   - generalization: the algorithm is given ε → the machine is given K = ⌈1/ε⌉; reason: the program knows less; specializes
--   - encoding: E_{X∼Q}[w(X)]; the remark 8ℓκ = Õ(ℓ) → the finite sum ∑_X Q(X)w(X); the remark is not a clause; reason: same quantity; the remark is a statement about the bound 8ℓκ, true by the definition of Õ
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Lemma 3.2, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_KnapsackFPRAS_feasible
import Definitions.Def_KnapsackFPRAS_Machine
import Definitions.Def_KnapsackFPRAS_Tilt

set_option autoImplicit false

namespace KnapsackFPRAS

/-- **Lemma 3.2**, p.12. "Let ℓ be the parameter returned by Lemma 2.4. There is an Õ(𝑛)-time
algorithm that, using O(log(𝑛/𝜀)) bits of numerical precision, returns a rational number
𝜆* = 𝑦*/𝑇, where 𝑦* is a number with O(log(𝑛/𝜀)) bits, such that |Ω| ≤ 𝐶^{𝜆*}_𝑤 ≤ 16𝑛|Ω|,
E_{𝑋∼𝑄^{𝜆*}_𝑤}[𝑤(𝑋)] ≤ 2𝑇, 𝜆*𝑇 ≤ 8ℓ𝜅 = Õ(ℓ)."

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Lemma 3.2, p.12 (PDF p.13).

**Formalization Note.** Under the standing assumption (7). The parameter `ℓ` is any power of two
in `[2, 8n)` satisfying (9) of Lemma 2.4, the properties of Lemma 2.4's output that the lemma
uses; it is given to the machine in cell `n + 3`, after the input layout of Theorem 1.1. One
program `P` and constants `c, c', C, k` come before the instance; every run halts within
`C·n·κ^k` steps (`κ = ⌈log₂(100n/ε)⌉`), with `y* = m/2^j` given by the mantissa `m` in cell 0
and the exponent `j` in cell 1, both of at most `c'κ` bits, and `λ* = y*/T`. The numerical
precision is that of the machine's words. The expectation is the finite sum
`∑_X Q^{λ*}_w(X) w(X)`. "= Õ(ℓ)" is a remark and not a clause. -/
theorem lemma_3_2 :
    ∃ P : List Machine.Instr, ∃ c c' C k : ℕ,
      ∀ (n : ℕ) (w : Fin n → ℕ) (T : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
        (∀ i, 1 ≤ w i ∧ w i ≤ T) → T < ∑ i, w i →
        ∀ ℓ : ℕ, (∃ b : ℕ, ℓ = 2 ^ b) → 2 ≤ ℓ → ℓ < 8 * n →
        2 * ∑ i ∈ Finset.univ.filter (fun i => (w i : ℝ) ≤ (T : ℝ) / ℓ), (w i : ℝ) < T →
        let K := ⌈1 / ε⌉₊
        let W := Machine.wordLen c n K T
        let κ := ⌈Real.logb 2 (100 * n / ε)⌉₊
        let x := Machine.input W n T K (fun i => min (w i) (T + 1)) [ℓ]
        ∀ ρ : ℕ → BitVec W, ∃ m, Machine.exec P ρ (C * n * κ ^ k) 0 0 x = some m ∧
          let y : ℝ := ((m 0).toNat : ℝ) / (2 : ℝ) ^ (m 1).toNat
          let lam : ℝ := y / T
          (m 0).toNat < 2 ^ (c' * κ) ∧ (m 1).toNat ≤ c' * κ ∧
          ((feasible w T).card : ℝ) ≤ Tilt.Cnorm (fun i => (w i : ℝ)) lam T ∧
          Tilt.Cnorm (fun i => (w i : ℝ)) lam T ≤ 16 * n * (feasible w T).card ∧
          Tilt.expWeight (fun i => (w i : ℝ)) lam ≤ 2 * T ∧
          lam * T ≤ 8 * ℓ * κ := by sorry

end KnapsackFPRAS
