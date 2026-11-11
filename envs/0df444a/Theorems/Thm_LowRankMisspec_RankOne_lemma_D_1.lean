-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_lemma_D_1
-- name    : LowRankMisspec.RankOne.lemma_D_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:18:45.369691+00:00
-- url     : https://prove2.me/theorems/f923f7ce-886b-4db3-8466-38b1ce73510f
-- title:
--   Lemma D.1 — empirical tree: $\mathrm{supp}\,\hat P\subseteq\mathrm{supp}\,P$, $\mathbb E\|P-\hat P\|_1\le\sqrt{2T(\sigma-1)/k}$, lazy sampling with $nTk$ CondSamp calls
-- statement:
--   There are one program of the fair-coin log-cost RAM, one exponent $c$ and one constant $C$ such that the following holds for every $T\ge1$, every $\sigma$, every integer $k\ge1$ and every law $P$ on $[\sigma]^T$. There is a random distribution $\hat P$ on $[\sigma]^T$ (finitely many outcomes $\omega$ with probabilities $w_\omega$, rational values) with
--   $$\mathrm{supp}(\hat P)\subseteq\mathrm{supp}(P),\qquad \mathbb E\|P-\hat P\|_1\le\sqrt{\frac{2T(\sigma-1)}{k}},\tag{9}$$
--   such that for every $n$ the program, run with $\mathrm{CondSamp}(P;\cdot)$ on input $[T,\sigma,k,n]$:
--   - outputs $n$ strings $X_1,\dots,X_n$ together with rationals $p_1,\dots,p_n>0$, and outputs a given $(x_i,p_i)_i$ with probability $\mathbb E_\omega\big[\prod_i\hat P_\omega[x_i]\cdot\mathbf 1\{p_i=\hat P_\omega[x_i]\ \forall i\}\big]$: conditionally on $\hat P$, $n$ independent samples from this same $\hat P$ with the exact numbers $\hat P[X_i]$;
--   - makes at most $nTk$ calls to CondSamp on every run, every one at a prefix of positive $P$-probability;
--   - when $k$ is a power of two, halts on every run within log-cost $(n+T+\sigma+k+2)^c$ (which includes reading oracle responses).
--
--   Moreover every positive value $\hat P_\omega[x]$ has encoding length $\mathrm{bits}(\text{num})+\mathrm{bits}(\text{den})\le C\,T\log(k+1)$, for every $k\ge1$ (in particular when $k$ is a power of two).
--
--   Corollary D.2 uses it, with $k$ a power of two, to draw validation samples with exact probabilities.
--
--   Differences from the source:
--   - generalization: §2.1 fixes σ, T ≥ 2 → T ≥ 1 and every σ; reason: Theorem 5.1's proof applies the lemma at T ≥ 1, σ ≥ 1; T ≥ 1 keeps the O(T log(k+1)) clause meaningful; at σ, T ≥ 2 the Lean statement is the source's
--   - generalization: there is a random distribution P̂ → there are a finite type Ω, a law w on Ω and rational laws P̂_ω (ω ∈ Ω); reason: a random distribution with finitely many rational-valued outcomes is a particular random distribution, so the Lean statement implies the printed one; the paper's empirical tree has this form
--   - encoding: symbols [σ] = {1, …, σ} and coordinates 1, …, T → Fin σ and Fin T (0-based: symbol a ↦ a − 1, coordinate j ↦ j − 1); reason: relabelling; same instances
--   - encoding: supp(P̂) ⊆ supp(P) → for every outcome ω and string x, P̂_ω x ≠ 0 → P x ≠ 0; reason: outcomes of probability zero can be dropped from a finite Ω
--   - encoding: generate n conditionally independent samples from this same P̂ together with the exact numbers P̂[X_i] > 0 → for every (x_i, p_i)_i with p_i > 0, outProb of that output = Σ_ω w_ω · 1{p_i = P̂_ω x_i ∀ i} · Π_i P̂_ω x_i, and every output has this form with p_i > 0; reason: the joint law of the n samples and their probabilities, written out on the machine's output cells
--   - encoding: at most nTk calls to CondSamp; every conditional query at a positive-probability prefix → QueriesWithin n·T·k and AllQueriesSatisfy (0 < prefMass P h), on every run; reason: worst case over all runs, as in Definition 2.2
--   - reading: worst-case bit complexity polynomial in n, T, σ, k → one exponent c with HaltsWithin (n + T + σ + k + 2)^c on every run; reason: a polynomial in these parameters is bounded by such a power; the input [T, σ, k, n] has encoding length below it
--   - encoding: encoding length O(T log(k + 1)) → bits(num) + bits(den) ≤ C·T·log(k + 1) with one universal C fixed before every instance; reason: the O(·) as an explicit universal constant
--   - generalization: "when k is a power of two, …, and each probability P̂[X_i] is a rational number with encoding length O(T log(k + 1))" → the encoding-length bound for every k ≥ 1, not only powers of two; reason: the sentence can be read with the condition covering this clause too; the Lean statement takes the stronger reading, which the proof supports for every k (a product of T counts over k^T, p. 32) and which specializes to the printed clause at k a power of two
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 31 (PDF 32), Lemma D.1

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Machine
import Definitions.Def_LowRankMisspec_RankOne_Laws
import Definitions.Def_LowRankMisspec_RankOne_Machine

open PrefixMixLearn.Proper (Program HaltsWithin QueriesWithin OutputsSatisfy outProb bits)

namespace LowRankMisspec.RankOne

/-- Lemma D.1 (empirical approximation of `P` with lazy access using CondSamp). There are one
fair-coin program, one exponent `c` and one constant `C` such that for all `T ≥ 1`, `σ`, `k ≥ 1`
and every law `P` on `[σ]^T` there is a random rational law `P̂` on `[σ]^T` (outcomes `ω` of a
finite set with probabilities `w ω`) with `supp(P̂) ⊆ supp(P)` and
`E‖P − P̂‖₁ ≤ √(2T(σ − 1)/k)`, such that for every `n`, run with `CondSamp(P; ·)` on `[T, σ, k, n]`:
the output is `n` strings `X_i` with rationals `p_i > 0`, and the probability of outputting
`(X_i, p_i)_i` is `E_ω[Π_i P̂_ω[X_i] · 1{p_i = P̂_ω[X_i] ∀ i}]` (conditionally on `P̂`, `n`
independent draws from this same `P̂` with their exact probabilities); every run makes at most
`nTk` oracle calls, each at a prefix of positive `P`-probability; and when `k` is a power of two,
every run halts within log-cost `(n + T + σ + k + 2)^c`. Every positive `P̂_ω[x]` has encoding
length at most `C·T·log(k + 1)` (for every `k ≥ 1`, which includes the powers of two). -/
theorem lemma_D_1 :
    ∃ (prog : Program) (c : ℕ) (C : ℝ),
      ∀ (T σ k : ℕ), 1 ≤ T → 1 ≤ k → ∀ (P : Str σ T → ℝ), IsLaw P →
        ∃ (Ω : Type) (_ : Fintype Ω) (w : Ω → ℝ) (Phat : Ω → Str σ T → ℚ),
          IsLaw w ∧
          (∀ ω, IsLaw fun x => (Phat ω x : ℝ)) ∧
          (∀ ω x, Phat ω x ≠ 0 → P x ≠ 0) ∧
          ∑ ω, w ω * l1 P (fun x => (Phat ω x : ℝ)) ≤
            Real.sqrt (2 * (T : ℝ) * ((σ : ℝ) - 1) / k) ∧
          (∀ ω x, 0 < Phat ω x →
            ((bits (Phat ω x).num.toNat + bits (Phat ω x).den : ℕ) : ℝ) ≤
              C * T * Real.log (k + 1)) ∧
          ∀ n : ℕ,
            (∀ (xs : Fin n → Str σ T) (ps : Fin n → ℚ), (∀ i, 0 < ps i) →
              outProb prog (condSamp P) (treeInput T σ k n) (fun o => o = samplesCells xs ps) =
                ∑ ω, w ω * (if ∀ i, ps i = Phat ω (xs i) then ∏ i, (Phat ω (xs i) : ℝ) else 0)) ∧
            OutputsSatisfy prog (condSamp P) (treeInput T σ k n)
              (fun o => ∃ (xs : Fin n → Str σ T) (ps : Fin n → ℚ),
                o = samplesCells xs ps ∧ ∀ i, 0 < ps i) ∧
            QueriesWithin prog (condSamp P) (treeInput T σ k n) ((n : ℝ) * T * k) ∧
            AllQueriesSatisfy prog (condSamp P) (treeInput T σ k n) (fun h => 0 < prefMass P h) ∧
            ((∃ j : ℕ, k = 2 ^ j) →
              HaltsWithin prog (condSamp P) (treeInput T σ k n)
                (((n + T + σ + k + 2 : ℕ) : ℝ) ^ c)) := by sorry

end LowRankMisspec.RankOne
