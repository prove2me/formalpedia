-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_7_2
-- name    : MatroidSensOracle.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:16:19.573801+00:00
-- url     : https://prove2.me/theorems/2219cf82-4511-4063-aece-26dd57f815ad
-- title:
--   Theorem 7.2 (parity-basis sensitivity), all four rows of Table 12
-- statement:
--   There is an absolute constant $C_{\mathrm{err}}$ such that the following holds. Let $\mathbb F$ be a finite field, $\omega=\omega_{\mathbb F}$, $\tau>0$, and let $M$ be a linear matroid of even rank $N$ over $\mathbb F$ whose elements are partitioned into $m$ pairs $(a_e,b_e)$ with integer weights in $[-W,W]$. A **parity basis** is a set of $N/2$ pairs whose $N$ columns form a basis. Queries are at most $f$ pair insertions and deletions.
--
--   There are constants $C,K,b$ and four oracles on the algebraic RAM over $\mathbb F$ deciding whether the updated matroid has a parity basis and, in the weighted rows, reporting its minimum weight; each fixed query is answered correctly with probability at least $1-C_{\mathrm{err}}N/|\mathbb F|$. With $\tilde O(X)=C\,X\log^K$:
--
--   1. **General, $k$-sparse, existence:** preprocessing $C(k^2m+N^{\omega+\tau})$, space $C(km+N^2)$, query $C(f^{\omega+\tau}+f^2k^2)$.
--   2. **General, $k$-sparse, minimum weight:** preprocessing $\tilde O(k^2m+WN^{\omega+1})$, space $C(km+WN^3)$, query $\tilde O(NW(f^{\omega}+f^2k^2))$.
--   3. **Subset, existence:** preprocessing $Cm^{\omega+\tau}$, space $C(m^\star)^2$, query $Cf^{\omega+\tau}$.
--   4. **Subset, minimum weight:** preprocessing $\tilde O(NWm^{\omega})$, space $C\,NW(m^\star)^2$, query $\tilde O(NWf^{\omega})$.
--
--   Here $m=|E|$ in the general and $m=|E\cup E^\star|$ in the subset setting; space is counted in cells. Through the reduction of §8 these oracles yield the $\alpha$-factor oracles of Theorems 8.3 and 9.12.
--
--   Differences from the source:
--   - reading: sensitivity oracles for a matroid represented over F (machine unstated) → oracles on the base algebraic RAM over the finite field F: time counts all instructions, worst case over the coins; space counts stored cells; error per fixed query; reason: the machine of the published base milestones Theorems 3.5 and 3.7
--   - encoding: O(x^ω), O(x^{ω+1}) → C·x^{ω+τ}, C·x^{ω+1+τ} for every τ > 0, with ω = omega F; reason: base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - encoding: a linear matroid whose elements are partitioned into pairs, with pair weights → a list of base elements, each a pair: its two columns a, b and its weight; rank N = some N of the 2m columns are independent (PairRankFull); reason: the base element encoding; inserted and deleted elements are whole pairs
--   - encoding: parameters N, m, k, f, W → N, m, k, f, W ≥ 1 (and m★ ≥ 1 in the subset setting); weights in [−W, W] in every row; reason: nondegeneracy as in the base settings; existence rows ignore the weights
--   - encoding: subset setting: updates confined to E★ with columns known at preprocessing → the base subset setting: ground set E ∪ E★ listed, deletions from E ∩ E★, insertions from E★ ∖ E; reason: the base SolvesSubset model, m = |E ∪ E★|
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - generalization: subset rows: M has rank N on the active pairs E → the 2m columns of all listed pairs E ∪ E★ have rank N (PairRankFull of the whole list); reason: rank N of E implies rank N of E ∪ E★ (both have N rows), so every instance of the source is covered
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 7.2, p.38 (PDF p.41)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_MatroidProblems
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 7.2 (Parity-basis sensitivity), with Table 12.** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.38 (PDF p.41): "Let M be a linear matroid of
even rank N whose elements are partitioned into pairs. Given at most f pair insertions and deletions,
the oracles in Table 12 decide whether the updated matroid has a parity basis and, for integer pair
weights in [−W, W], report the minimum weight of such a basis if one exists. Each fixed query is
answered correctly with probability at least 1 − O(N/|F|)."

| Setting | Objective | Preprocessing time | Space | Query time |
|---|---|---|---|---|
| General, k-sparse | Existence | O(k²m + N^ω) | O(km + N²) | O(f^ω + f²k²) |
| General, k-sparse | Minimum weight | Õ(k²m + WN^{ω+1}) | O(km + WN³) | Õ(NW(f^ω + f²k²)) |
| Subset | Existence | O(m^ω) | O((m★)²) | O(f^ω) |
| Subset | Minimum weight | Õ(NWm^ω) | O(NW(m★)²) | Õ(NWf^ω) |

"Here m = |E| in the general setting and m = |E ∪ E★| in the subset setting."

**Formalization Note.**
* Machine and semantics as in the base `theorem_3_5`: algebraic RAM over `F`, `ω = omega F`,
  `O(x^ω) = C x^{ω+τ}`, error `Cerr N / |F|` with `Cerr` chosen before the field. `Õ(X)` is
  `C X (log₂(Z + 2))^K` where `Z` is the sum of the parameters occurring in `X`.
* Each base element `Elem F N` is a pair: columns `a`, `b`, weight `wt ∈ [−W, W]`; insertions insert
  whole pairs. A parity basis is a set of `N/2` pairs whose `N` columns are independent
  (`IsParityBasis`); the weighted rows also return `minParityWeight`.
* Hypotheses: `N` even and the matroid has rank `N` (`PairRankFull`): of the original pairs in the
  general setting, of all listed pairs `E ∪ E★` in the subset setting. General setting: original and
  inserted columns `k`-sparse. -/
theorem theorem_7_2 :
    ∃ Cerr : ℝ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ O₃ O₄ : AOracle),
      let ω := OAI.MatrixMultiplication.Arithmetic.omega F
      let q : ℝ := Fintype.card F
      let lg : ℕ → ℝ := fun Z => Real.logb 2 ((Z : ℝ) + 2)
      let prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ :=
        fun _ _ L => (∃ S, IsParityBasis L S, minParityWeight L)
      let admG : (N k W : ℕ) → List (Elem F N) → Prop := fun N k W L =>
        PairRankFull L ∧ Even N ∧ ∀ x ∈ L, Sparse k x.a ∧ Sparse k x.b ∧ |x.wt| ≤ W
      let insG : (N k W : ℕ) → Elem F N → Prop := fun _ k W x => Sparse k x.a ∧ Sparse k x.b ∧ |x.wt| ≤ W
      let admS : (N k W : ℕ) → (L : List (Elem F N)) → Finset (Fin L.length) → Finset (Fin L.length) →
        Prop := fun N _ _ L _ _ => PairRankFull L ∧ Even N
      -- General, k-sparse, existence
      O₁.SolvesGeneralOn b admG insG false prob false
        (fun N m k _ _ => C * ((k : ℝ) ^ 2 * m + (N : ℝ) ^ (ω + τ)))
        (fun N m k _ _ => C * ((k : ℝ) * m + (N : ℝ) ^ 2))
        (fun _ _ k f _ => C * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2))
        (fun N _ _ _ _ => Cerr * N / q) ∧
      -- General, k-sparse, minimum weight
      O₂.SolvesGeneralOn b admG insG false prob true
        (fun N m k _ W => C * ((k : ℝ) ^ 2 * m + W * (N : ℝ) ^ (ω + 1 + τ)) * lg (k + m + W + N) ^ K)
        (fun N m k _ W => C * ((k : ℝ) * m + W * (N : ℝ) ^ 3))
        (fun N _ k f W =>
          C * (N * W * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2)) * lg (N + W + f + k) ^ K)
        (fun N _ _ _ _ => Cerr * N / q) ∧
      -- Subset, existence
      O₃.SolvesSubsetOn b admS prob false
        (fun _ m _ _ _ _ => C * (m : ℝ) ^ (ω + τ))
        (fun _ _ ms _ _ _ => C * (ms : ℝ) ^ 2)
        (fun _ _ _ _ f _ => C * (f : ℝ) ^ (ω + τ))
        (fun N _ _ _ _ _ => Cerr * N / q) ∧
      -- Subset, minimum weight
      O₄.SolvesSubsetOn b admS prob true
        (fun N m _ _ _ W => C * (N * W * (m : ℝ) ^ (ω + τ)) * lg (N + W + m) ^ K)
        (fun N _ ms _ _ W => C * (N * W * (ms : ℝ) ^ 2))
        (fun N _ _ _ f W => C * (N * W * (f : ℝ) ^ (ω + τ)) * lg (N + W + f) ^ K)
        (fun N _ _ _ _ _ => Cerr * N / q) := by sorry

end MatroidSensOracle.Supplement
