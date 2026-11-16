-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_5_9
-- name    : MatroidSensOracle.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:12:14.677546+00:00
-- url     : https://prove2.me/theorems/88b53993-e2fb-4948-8523-d2aff1d28e8b
-- title:
--   Theorem 5.9 (global min-cut value and partition oracles), partition query $\tilde O(f^5+f^{3\omega}n)$
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex directed graph with unit edge capacities and integer edge costs in $[-W,W]$. Its global min-cut value is $\mu_G=\min_{s\in V}\mu_G(s)$, and a global min-cut is a nonempty proper vertex set $A$ whose out-capacity is $\mu_G$. Let $T_{\mathrm{aug}}$ be as in Theorem 5.8.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K$ such that for every optimal-augmentation algorithm with running time $T_{\mathrm{aug}}(n,f)$ there are two oracles on the randomized word RAM answering every fixed query (a set $U$ of at most $f$ edge insertions and deletions) wrongly with probability at most $n^{-c}$:
--
--   1. **Global min-cut value:** preprocessing $C\bigl(f^{\omega+\tau}n^{\omega+1+\tau}+T_{\mathrm{aug}}(n,f)\bigr)$, space $Cf^2n^3\log_2 n$ bits, query $\tilde O(f^5)$; output $\mu_{G+U}$.
--   2. **Global min-cut partition:** the same preprocessing and space, query $\tilde O(f^5+f^{3\omega}n)$; output a global min-cut of $G+U$.
--
--   **Formalization Note** $f^{3\omega}$ is read as $f^{3\omega+\tau}$ for every $\tau>0$. The costs are printed in the theorem and kept in the instance, although the outputs do not depend on them.
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - generalization: T_aug, the polynomial time of the augmentation algorithm of Theorem 5.6 ([48]) → for every word-RAM program A that outputs an optimal augmentation within TA(n, f) steps on every instance, preprocessing within C·(printed term + TA(n, f)), C and K independent of A; reason: specializes to the paper's claim with A the algorithm inferred from [48]; the proofs use A as a black box
--   - reading: I∗ ⊆ V × V of f edges maximizing μ_{G+I}(s) → a list of f pairs inserted as new (possibly parallel) edges, maximal among all such lists; reason: queries insert new edges of a multigraph; Lemma 5.7's μ_{G+U}(s) ≤ μ_{G+I∗}(s) needs the maximum over these insertions
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, f ≥ 1, W ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
--   - encoding: outputs μ_{G+U} and a global min-cut → word 0; the low bits of words 0, …, n − 1 mark a nonempty proper vertex set; reason: base output convention
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 5.9, pp.31–32 (PDF pp.34–35)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 5.9 (global min-cut oracles).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version,
sha256 0de50841…), pp.31–32 (PDF pp.34–35): "Let G = (V, E, c) be an n-vertex directed graph with unit
edge capacities and integer edge costs in [−W, W]. There exist the following sensitivity oracles
that, for any update set U of size ⩽ f, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Global Min-Cut Value | O(f^ω n^{ω+1} + T_aug) | O(f²n³ log n) | Õ(f⁵) | μ_{G+U} |
| Global Min-Cut Partition | O(f^ω n^{ω+1} + T_aug) | O(f²n³ log n) | Õ(f⁵ + f^{3ω} n) | Global-min-cut in G + U |

**Formalization Note.**
* `T_aug` is read parametrically as in `theorem_5_8`: for every program `A` computing optimal
  augmentations within `TA n f` steps (`AugAlgorithm`), the preprocessing time is at most
  `C (f^{ω+τ} n^{ω+1+τ} + TA n f)` with `C`, `K` independent of `A`.
* Machine, oracle semantics, `ω = omega ℂ`, `O(x^ω)`, `Õ`, space in bits and "with high
  probability" as in `theorem_5_8`. `P` reads `encodeWith G [n, f, W]`. `f^{3ω}` is read as
  `f^{3ω+τ}` for every `τ > 0`.
* Instances: `n ≥ 2`, `f ≥ 1`, `W ≥ 1`, costs in `[−W, W]` (printed; the outputs ignore them).
  Queries: any update set of at most `f` insertions and deletions with inserted costs in `[−W, W]`.
* Outputs: word `0` is `μ_{G+U} = min_s μ_{G+U}(s)`; the low bits of words `0, …, n − 1` mark a
  nonempty proper vertex set of out-capacity `μ_{G+U}`. -/
theorem theorem_5_9 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K : ℕ),
      ∀ (A : List Instr) (bA : ℕ) (TA : ℕ → ℕ → ℝ), AugAlgorithm A bA TA →
      ∃ (b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n f W : ℕ) (G : InputGraph n), 2 ≤ n → 1 ≤ f → 1 ≤ W → G.CostsBounded W →
        ∀ w : ℕ, b * (Nat.log 2 (n + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeWith G [(n : ℤ), f, W]
          let err : ℝ := (n : ℝ) ^ (-c)
          let Qs : Set (Update n) := {U | G.ValidUpdate f W U}
          let TP : ℕ := ⌊C * ((f : ℝ) ^ (ω + τ) * (n : ℝ) ^ (ω + 1 + τ) + TA n f)⌋₊
          let space : ℝ := C * (f : ℝ) ^ 2 * (n : ℝ) ^ 3 * Real.logb 2 n
          -- Global Min-Cut Value
          O₁.Serves w inp TP space Qs Update.encode
            ⌊C * (f : ℝ) ^ 5 * Real.logb 2 ((f : ℝ) + 2) ^ K⌋₊
            (fun U mQ => (mQ 0).toNat = globalMinCutValue (G.plus U)) err ∧
          -- Global Min-Cut Partition
          O₂.Serves w inp TP space Qs Update.encode
            ⌊C * ((f : ℝ) ^ 5 + (f : ℝ) ^ (3 * ω + τ) * n) *
              Real.logb 2 ((f + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => IsGlobalMinCut (G.plus U) (outSet mQ)) err := by sorry

end MatroidSensOracle.Supplement
