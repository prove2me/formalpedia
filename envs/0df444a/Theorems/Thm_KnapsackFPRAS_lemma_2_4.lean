-- Prove2me | Theorems.Thm_KnapsackFPRAS_lemma_2_4
-- name    : KnapsackFPRAS.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:33:59.220738+00:00
-- url     : https://prove2.me/theorems/1b0a66e6-8176-40a2-8853-9ef5ac5afcda
-- title:
--   Lemma 2.4 — a popular weight scale $\ell$, found in $\tilde O(n)$ word-RAM time
-- statement:
--   Assume $1\le w_i\le T$ for all $i$ and $\sum_i w_i>T$ (the standing assumption (7)). Let $0<\varepsilon<1$, $\kappa=\lceil\log_2(100n/\varepsilon)\rceil$ and $L:=\lceil\log_2(4n)\rceil$.
--
--   There are a program $P$ of the randomized word RAM and constants $c,C,k$ such that, for every such instance, on the input $(n,T,\lceil1/\varepsilon\rceil,w_1,\dots,w_n)$ with words of $c(\lfloor\log_2(n+1)\rfloor+\lfloor\log_2\lceil1/\varepsilon\rceil\rfloor+\lfloor\log_2(T+1)\rfloor+1)$ bits, every run of $P$ halts within $Cn\kappa^k$ steps and outputs a number $\ell$ with:
--
--   1. $\ell$ is a power of two and $2\le\ell<8n$;
--   2. the light items have small total weight:
--   $$
--   \sum_{i:\,w_i\le T/\ell}w_i<\frac T2; \tag{9}
--   $$
--   3. for every integer $d\ge1$, the excess layer $\Omega_d:=\{X\subseteq[n]: T+(d-1)T/\ell<w(X)\le T+dT/\ell\}$ satisfies
--   $$
--   |\Omega_d|\le n^d|\Omega|; \tag{10}
--   $$
--   4. the first layer satisfies
--   $$
--   |\Omega_1|\le\frac{15000\,nL^2}{\ell}\,|\Omega|. \tag{11}
--   $$
--
--   The scale $T/\ell$ is where the tilt of Lemma 3.2 is placed: (9) bounds the tilt, and (10)–(11) bound the subsets just above capacity. The paper cites the lemma to Feng and Jin.
--
--   Differences from the source:
--   - reading: the lemma as printed in §2 → hypotheses 1 ≤ wᵢ ≤ T and T < ∑ wᵢ; reason: standing assumption (7) of §2 (p.9), stated once for the rest of the paper
--   - reading: in Õ(n) time one can find ℓ → one program P of the machine of Theorem 1.1, chosen with c, C, k before the instance, every run of which halts within C·n·κ^k steps with ℓ in cell 0 satisfying every clause; reason: the paper's model is the word RAM of Theorem 1.1; the proof of Theorem 1.1 budgets no failure probability for this step, so the output is correct on every run (a deterministic algorithm is such a program)
--   - encoding: Õ(n) → C·n·κ^k with κ = ⌈log₂(100n/ε)⌉; reason: Õ suppresses polylog(n/ε) factors (§2, p.9) and κ = Θ(log(n/ε)) for n ≥ 2, which (7) forces
--   - generalization: the algorithm is given ε → the machine is given K = ⌈1/ε⌉ in the input layout of Theorem 1.1 (weights min(wᵢ, T+1) = wᵢ under (7)); reason: the program knows less; a program for this input also serves an exactly given ε
--   - encoding: T/ℓ, Ω_d, L = ⌈log₂(4n)⌉, [n] → real thresholds, Nat.clog 2 (4n), Fin n; reason: Lean conventions; same instances
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Lemma 2.4, p.10 (PDF p.11), Eqs. (9)–(11); cited to [FJ25, Lemmas 3.1–3.3 and (6)]

import Mathlib
import Definitions.Def_KnapsackFPRAS_feasible
import Definitions.Def_KnapsackFPRAS_Machine

set_option autoImplicit false

namespace KnapsackFPRAS

/-- **Lemma 2.4** (Popular weight class), p.9. "Let 𝐿 := ⌈log₂(4𝑛)⌉. In Õ(𝑛) time one can find a
power of two ℓ ∈ [2, 8𝑛) such that ∑_{𝑖 : 𝑤𝑖 ≤ 𝑇/ℓ} 𝑤𝑖 < 𝑇/2. (9) For every integer 𝑑 ≥ 1,
define the excess layer Ω_𝑑 := {𝑋 ⊆ [𝑛] : 𝑇 + (𝑑−1)𝑇/ℓ < 𝑤(𝑋) ≤ 𝑇 + 𝑑𝑇/ℓ}. Then
|Ω_𝑑| ≤ 𝑛^𝑑 |Ω| (𝑑 ≥ 1), (10) and |Ω₁| ≤ (15000 𝑛 𝐿²/ℓ) |Ω|. (11)"

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Lemma 2.4, p.10 (PDF p.11); the page cites it to [FJ25, Lemmas 3.1–3.3 and (6)].

**Formalization Note.** Under the standing assumption (7) of §2 (`1 ≤ wᵢ ≤ T`,
`∑ wᵢ > T`). "In Õ(n) time one can find" is a program `P` of the machine of Theorem 1.1, with
constants `c, C, k` chosen before the instance, started on the input layout of Theorem 1.1
(`min(wᵢ, T+1) = wᵢ` under (7)); every run halts within `C·n·κ^k` steps,
`κ = ⌈log₂(100n/ε)⌉` (Õ is defined through `n/ε` in §2, so `ε` is part of the input), and
leaves in cell 0 a number `ℓ` with all the properties of the lemma. "Every run" (not "with
probability"): the proof of Theorem 1.1 budgets no failure probability for this step. `T/ℓ` and
the excess layers are real. `L = Nat.clog 2 (4n) = ⌈log₂(4n)⌉`. -/
theorem lemma_2_4 :
    ∃ P : List Machine.Instr, ∃ c C k : ℕ,
      ∀ (n : ℕ) (w : Fin n → ℕ) (T : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
        (∀ i, 1 ≤ w i ∧ w i ≤ T) → T < ∑ i, w i →
        let K := ⌈1 / ε⌉₊
        let W := Machine.wordLen c n K T
        let κ := ⌈Real.logb 2 (100 * n / ε)⌉₊
        let x := Machine.input W n T K (fun i => min (w i) (T + 1)) []
        let L := Nat.clog 2 (4 * n)
        let wt := fun X : Finset (Fin n) => ∑ i ∈ X, (w i : ℝ)
        ∀ ρ : ℕ → BitVec W, ∃ m, Machine.exec P ρ (C * n * κ ^ k) 0 0 x = some m ∧
          let ℓ := (m 0).toNat
          let excess := fun d : ℕ => Finset.univ.filter (fun X : Finset (Fin n) =>
            (T : ℝ) + ((d : ℝ) - 1) * T / ℓ < wt X ∧ wt X ≤ (T : ℝ) + d * T / ℓ)
          (∃ b : ℕ, ℓ = 2 ^ b) ∧ 2 ≤ ℓ ∧ ℓ < 8 * n ∧
          2 * ∑ i ∈ Finset.univ.filter (fun i => (w i : ℝ) ≤ (T : ℝ) / ℓ), (w i : ℝ) < T ∧
          (∀ d : ℕ, 1 ≤ d → (excess d).card ≤ n ^ d * (feasible w T).card) ∧
          ((excess 1).card : ℝ) ≤ 15000 * n * (L : ℝ) ^ 2 / ℓ * (feasible w T).card := by sorry

end KnapsackFPRAS
