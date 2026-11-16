-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_5_8
-- name    : MatroidSensOracle.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:11:15.511482+00:00
-- url     : https://prove2.me/theorems/14f03681-8969-44db-891b-9fdf8bbbdc26
-- title:
--   Theorem 5.8 ($s$-min-cut value and partition oracles), preprocessing $O(f^\omega n^{\omega+1}+T_{\mathrm{aug}})$
-- statement:
--   Let $G=(V,E)$ be an $n$-vertex directed graph with unit capacities and let $s\in V$. Write
--   $$\mu_G(s)=\min_{v\in V\setminus\{s\}}\lambda_G(s,v)$$
--   for the $s$-min-cut value; an $s$-min-cut is a vertex set $A\ni s$, $A\ne V$, whose out-capacity is $\mu_G(s)$. Let $T_{\mathrm{aug}}$ be the running time of an algorithm that, given $(G,s,f)$, outputs $f$ new edges whose insertion maximizes the $s$-min-cut value (Theorem 5.6, [48]).
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K$ such that for every such augmentation algorithm, with running time $T_{\mathrm{aug}}(n,f)$, there are two oracles on the randomized word RAM answering every fixed query (a set $U$ of at most $f$ edge insertions and deletions) wrongly with probability at most $n^{-c}$:
--
--   1. **$s$-min-cut value:** preprocessing $C\bigl(f^{\omega+\tau}n^{\omega+1+\tau}+T_{\mathrm{aug}}(n,f)\bigr)$, space $C f^2n^3\log_2 n$ bits, query $\tilde O(f^5)$; output $\mu_{G+U}(s)$.
--   2. **$s$-min-cut partition:** the same preprocessing and space, query $\tilde O(f^5+f^4n)$; output an $s$-min-cut of $G+U$.
--
--   These oracles lift the fixed-pair oracles of Theorem 5.5 to rooted cuts and give the global min-cut oracles of Theorem 5.9.
--
--   **Formalization Note** The augmentation step is a parameter: the theorem holds for every program solving it, with $C$ and $K$ independent of the program.
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - generalization: T_aug, the polynomial time of the augmentation algorithm of Theorem 5.6 ([48]) → for every word-RAM program A that outputs an optimal augmentation within TA(n, f) steps on every instance, preprocessing within C·(printed term + TA(n, f)), C and K independent of A; reason: specializes to the paper's claim with A the algorithm inferred from [48]; the proofs use A as a black box
--   - reading: I∗ ⊆ V × V of f edges maximizing μ_{G+I}(s) → a list of f pairs inserted as new (possibly parallel) edges, maximal among all such lists; reason: queries insert new edges of a multigraph; Lemma 5.7's μ_{G+U}(s) ≤ μ_{G+I∗}(s) needs the maximum over these insertions
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, f ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
--   - encoding: outputs μ_{G+U}(s) and an s-min-cut → word 0; the low bits of words 0, …, n − 1 mark the source side A ∋ s, A ≠ V; reason: base output convention
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 5.8, p.31 (PDF p.34)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 5.8 (`s`-min-cut oracles).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version,
sha256 0de50841…), p.31 (PDF p.34): "Let G = (V, E, c) be an n-vertex directed graph, and let s ∈ V.
Then there exist the following sensitivity oracles that, for any set of edge updates U where
|U| ⩽ f, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| s-Min-Cut Value | O(f^ω n^{ω+1} + T_aug) | O(f²n³ log n) | Õ(f⁵) | μ_{G+U}(s) |
| s-Min-Cut Partition | O(f^ω n^{ω+1} + T_aug) | O(f²n³ log n) | Õ(f⁵ + f⁴n) | s-min-cut in G + U |

p.30: "T_aug" is the polynomial running time of the optimal augmentation of Theorem 5.6 ([48]).

**Formalization Note.**
* `T_aug` is read parametrically: for every word-RAM program `A` that computes an optimal
  augmentation (`AugAlgorithm A bA TA`: on every `(G, s, f)` a list of `f` new edges maximizing
  `μ_{G+I}(s)`, within `TA n f` steps), there are oracles whose preprocessing time is at most
  `C (f^{ω+τ} n^{ω+1+τ} + TA n f)`; `C` and `K` do not depend on `A`, the word-width constant `b` and
  the programs may.
* Machine and oracle semantics: the base randomized word RAM; `P` reads `encodeWith G [n, f, s]`, `Q`
  reads only the stored string and `U.encode`. `ω = omega ℂ`; `O(x^ω)` is `C x^{ω+τ}` for every
  `τ > 0`; `Õ(X)` is `C X (log₂(Z + 2))^K`, `Z` the sum of the parameters in `X`; `log n = log₂ n`.
  Space in bits.
* With high probability: for every `c > 0` each fixed query errs with probability at most `n^{−c}`.
* Instances: `n ≥ 2`, `f ≥ 1`; no cost bound is printed and the outputs ignore costs. Queries: any
  update set of at most `f` insertions and deletions (`F ⊆ E`); `G + U` is a multigraph.
* Outputs: word `0` is `μ_{G+U}(s) = min_{v ≠ s} λ_{G+U}(s, v)`; the low bits of words
  `0, …, n − 1` mark a vertex set `A ∋ s`, `A ≠ V`, of out-capacity `μ_{G+U}(s)`. -/
theorem theorem_5_8 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K : ℕ),
      ∀ (A : List Instr) (bA : ℕ) (TA : ℕ → ℕ → ℝ), AugAlgorithm A bA TA →
      ∃ (b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n f : ℕ) (G : InputGraph n) (s : Fin n), 2 ≤ n → 1 ≤ f →
        ∀ w : ℕ, b * (Nat.log 2 (n + f + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeWith G [(n : ℤ), f, (s : ℕ)]
          let err : ℝ := (n : ℝ) ^ (-c)
          let Qs : Set (Update n) := {U | G.ValidPlain f U}
          let TP : ℕ := ⌊C * ((f : ℝ) ^ (ω + τ) * (n : ℝ) ^ (ω + 1 + τ) + TA n f)⌋₊
          let space : ℝ := C * (f : ℝ) ^ 2 * (n : ℝ) ^ 3 * Real.logb 2 n
          -- s-Min-Cut Value
          O₁.Serves w inp TP space Qs Update.encode
            ⌊C * (f : ℝ) ^ 5 * Real.logb 2 ((f : ℝ) + 2) ^ K⌋₊
            (fun U mQ => (mQ 0).toNat = sMinCutValue (G.plus U) s) err ∧
          -- s-Min-Cut Partition
          O₂.Serves w inp TP space Qs Update.encode
            ⌊C * ((f : ℝ) ^ 5 + (f : ℝ) ^ 4 * n) * Real.logb 2 ((f + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => IsSMinCut (G.plus U) s (outSet mQ)) err := by sorry

end MatroidSensOracle.Supplement
