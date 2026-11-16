-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_5
-- name    : MatroidSensOracle.Supplement.theorem_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:22:11.411579+00:00
-- url     : https://prove2.me/theorems/31d670fd-6b4a-4dda-a403-1549ce39af61
-- title:
--   Theorem 9.5 (subset global min-cut value and partition oracles), space $O(\sigma^3)$ / $O(\sigma^3+\sigma n^2)$
-- statement:
--   Let $G=(V,E)$ be an $n$-vertex directed graph with $m$ edges and a susceptible set $E_Q$ of $\sigma\ge1$ pairs (possibly not in $E$). Queries are $U\subseteq E_Q$ with $|U|\le f$, toggling their pairs. Let $T_{\mathrm{aug}}$ be as in Theorem 5.8, with a time bound nondecreasing in $f$.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K$ such that for every such augmentation algorithm there are two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **global min-cut value:** preprocessing $C\bigl(\sigma m^{1+\tau}+\sigma^3(fn)^{\omega-2+\tau}+T_{\mathrm{aug}}(n,f)\bigr)$, space $C\sigma^3$ words, query $\tilde O(f^{\omega+1})$; output $\mu_{G+U}$.
--   2. **global min-cut partition:** preprocessing $C\bigl((\sigma^3+\sigma n^2)(fn)^{\omega-2+\tau}+T_{\mathrm{aug}}(n,f)\bigr)$, space $C(\sigma^3+\sigma n^2)$ words, query $\tilde O(f^{\omega}n)$; output a global min-cut of $G+U$.
--
--   These are the subset-model counterparts of Theorems 5.8 and 5.9.
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - generalization: a susceptible set E_Q ⊆ E; updates U ⊆ E_Q consisting of insertions and deletions → E_Q any set of pairs (with costs), possibly not in E; a query U ⊆ E_Q, |U| ≤ f, deletes U ∩ E and inserts U ∖ E; reason: §9.1: E_Q 'may include edges not currently in E'; the printed E_Q ⊆ E is the special case
--   - encoding: a susceptible set of size m★ → m★ = |E_Q| ≥ 1; reason: an O((m★)²) space bound is 0 at m★ = 0, where no oracle can answer; as in the base subset setting (1 ≤ m★)
--   - generalization: T_aug, the polynomial time of the augmentation algorithm of Theorem 5.6 ([48]) → for every word-RAM program A that outputs an optimal augmentation within TA(n, f) steps on every instance, preprocessing within C·(printed term + TA(n, f)), C and K independent of A; reason: specializes to the paper's claim with A the algorithm inferred from [48]; the proofs use A as a black box
--   - reading: I∗ ⊆ V × V of f edges maximizing μ_{G+I}(s) → a list of f pairs inserted as new (possibly parallel) edges, maximal among all such lists; reason: queries insert new edges of a multigraph; Lemma 5.7's μ_{G+U}(s) ≤ μ_{G+I∗}(s) needs the maximum over these insertions
--   - reading: T_aug (polynomial time) → the time bound TA(n, f) of the augmentation program is nondecreasing in f; reason: the polynomial running time of [48] is nondecreasing; an oracle may run the augmentation for min(f, |E_Q|) edges since |U| ≤ |E_Q|
--   - encoding: m^{1+o(1)} → C·m^{1+τ} for every τ > 0; reason: o(1) in an exponent
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, f ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.5, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.5 (subset global min-cut oracles).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held
version, sha256 0de50841…), p.49 (PDF p.52): "Let G = (V, E, c) be an n-vertex directed graph with a
susceptible set E_Q ⊆ E of size σ. Then there exist the following subset sensitivity oracles that, for
any update set U ∈ E_Q^f consisting of insertions and deletions, answer queries on G + U with high
probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Global Min-Cut Value | O(σ m^{1+o(1)} + σ³(fn)^{ω−2} + T_aug) | O(σ³) | Õ(f^{ω+1}) | μ_{G+U} |
| Global Min-Cut Partition | O((σ³ + σn²)(fn)^{ω−2} + T_aug) | O(σ³ + σn²) | Õ(f^ω n) | Global min-cut in G + U |

**Formalization Note.**
* `T_aug`, the subset model, machine, oracle semantics, asymptotics, space units and "with high
  probability" as in `theorem_9_4`. `P` reads `encodeSubset G [n, f] E_Q ∅`, `Q` reads `pairWords U`.
* Instances: `n ≥ 2`, `f ≥ 1`, `σ = |E_Q| ≥ 1`; no cost bound is printed. Outputs as in
  `theorem_5_9`. -/
theorem theorem_9_5 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K : ℕ),
      ∀ (A : List Instr) (bA : ℕ) (TA : ℕ → ℕ → ℝ), AugAlgorithm A bA TA → (∀ n, Monotone (TA n)) →
      ∃ (b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n f : ℕ) (G : InputGraph n) (EQ : Finset (Fin n × Fin n)),
        2 ≤ n → 1 ≤ f → 1 ≤ EQ.card → ∀ w : ℕ, b * (Nat.log 2 (n + f + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeSubset G [(n : ℤ), f] EQ ∅
          let err : ℝ := (n : ℝ) ^ (-c)
          let fn : ℝ := (f : ℝ) * n
          let m : ℝ := (pairList n G.E).length
          let σ : ℝ := EQ.card
          let Qs : Set (Finset (Fin n × Fin n)) := {U | U ⊆ EQ ∧ U.card ≤ f}
          let H : Finset (Fin n × Fin n) → CostMultigraph (Fin n) := fun U => G.plus (G.toggle U)
          -- Global Min-Cut Value
          O₁.Serves w inp ⌊C * (σ * m ^ (1 + τ) + σ ^ 3 * fn ^ (ω - 2 + τ) + TA n f)⌋₊
            (C * σ ^ 3 * w) Qs pairWords
            ⌊C * (f : ℝ) ^ (ω + 1 + τ) * Real.logb 2 ((f : ℝ) + 2) ^ K⌋₊
            (fun U mQ => (mQ 0).toNat = globalMinCutValue (H U)) err ∧
          -- Global Min-Cut Partition
          O₂.Serves w inp ⌊C * ((σ ^ 3 + σ * (n : ℝ) ^ 2) * fn ^ (ω - 2 + τ) + TA n f)⌋₊
            (C * (σ ^ 3 + σ * (n : ℝ) ^ 2) * w) Qs pairWords
            ⌊C * (f : ℝ) ^ (ω + τ) * n * Real.logb 2 ((f + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => IsGlobalMinCut (H U) (outSet mQ)) err := by sorry

end MatroidSensOracle.Supplement
