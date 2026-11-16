-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_7_3
-- name    : MatroidSensOracle.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:17:13.409963+00:00
-- url     : https://prove2.me/theorems/069157d6-c587-4b9f-92ba-99451e6f8479
-- title:
--   Theorem 7.3 ($k$-parity sensitivity), all four rows of Table 13
-- statement:
--   Let $c$ be a sparsity constant. There is a constant $C_{\mathrm{err}}$ (depending on $c$ only) such that the following holds. Let $\mathbb F$ be a finite field, $\omega=\omega_{\mathbb F}$, $\tau>0$, and let $M$ be a rank-$N$ linear matroid over $\mathbb F$ whose elements are partitioned into pairs with integer weights in $[-W,W]$, with $kN$ even. A **$k$-parity basis** is a set of $kN/2$ pairs whose $kN$ elements can be partitioned into $k$ bases of $M$; the two elements of a pair may lie in different bases. Queries are at most $f$ pair insertions and deletions.
--
--   There are constants $C,K,b$ and four oracles on the algebraic RAM over $\mathbb F$ deciding whether a $k$-parity basis exists and, in the weighted rows, reporting its minimum weight; each fixed query is answered correctly with probability at least $1-C_{\mathrm{err}}kN/|\mathbb F|$:
--
--   1. **General, $O(1)$-sparse, existence:** preprocessing $C(k^2m+(kN)^{\omega+\tau})$, space $C(km+(kN)^2)$, query $C(f^{\omega+\tau}+f^2k^2)$.
--   2. **General, $O(1)$-sparse, minimum weight:** preprocessing $\tilde O(k^2m+W(kN)^{\omega+1})$, space $C(km+W(kN)^3)$, query $\tilde O(WkN(f^{\omega}+f^2k^2))$.
--   3. **Subset, existence:** preprocessing $Cm^{\omega+\tau}$, space $C(m^\star)^2$, query $Cf^{\omega+\tau}$.
--   4. **Subset, minimum weight:** preprocessing $\tilde O(WkNm^{\omega})$, space $C\,WkN(m^\star)^2$, query $\tilde O(WkNf^{\omega})$.
--
--   Here $m=|E|$ in the general and $m=|E\cup E^\star|$ in the subset setting; space is counted in cells; in the general rows original and inserted columns are $c$-sparse.
--
--   Differences from the source:
--   - reading: sensitivity oracles for a matroid represented over F (machine unstated) → oracles on the base algebraic RAM over the finite field F: time counts all instructions, worst case over the coins; space counts stored cells; error per fixed query; reason: the machine of the published base milestones Theorems 3.5 and 3.7
--   - encoding: O(x^ω), O(x^{ω+1}) → C·x^{ω+τ}, C·x^{ω+1+τ} for every τ > 0, with ω = omega F; reason: base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - encoding: a linear matroid whose elements are partitioned into pairs, with pair weights → a list of base elements, each a pair: its two columns a, b and its weight; rank N = some N of the 2m columns are independent (PairRankFull); reason: the base element encoding; inserted and deleted elements are whole pairs
--   - encoding: parameters N, m, k, f, W → N, m, k, f, W ≥ 1 (and m★ ≥ 1 in the subset setting); weights in [−W, W] in every row; reason: nondegeneracy as in the base settings; existence rows ignore the weights
--   - encoding: subset setting: updates confined to E★ with columns known at preprocessing → the base subset setting: ground set E ∪ E★ listed, deletions from E ∩ E★, insertions from E★ ∖ E; reason: the base SolvesSubset model, m = |E ∪ E★|
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - encoding: O(1)-sparse columns (general rows) → for every constant c, columns c-sparse; constants depend on c; reason: the printed setting of Table 13
--   - generalization: subset rows: M has rank N on the active pairs E → the 2m columns of all listed pairs E ∪ E★ have rank N (PairRankFull of the whole list); reason: rank N of E implies rank N of E ∪ E★ (both have N rows), so every instance of the source is covered
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 7.3, pp.38–39 (PDF pp.41–42)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_MatroidProblems
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 7.3 (k-parity sensitivity), with Table 13.** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), pp.38–39 (PDF pp.41–42): "Let M be a rank-N
linear matroid over F whose elements are partitioned into pairs, and suppose kN is even. The oracles
in Table 13 decide whether a k-parity basis exists after at most f pair insertions and deletions. For
integer pair weights in [−W, W], the weighted oracles report its minimum possible weight, or report
that none exists. Each fixed query is answered correctly with probability at least 1 − O(kN/|F|)."

| Setting | Objective | Preprocessing time | Space | Query time |
|---|---|---|---|---|
| General, O(1)-sparse | Existence | O(k²m + (kN)^ω) | O(km + (kN)²) | O(f^ω + f²k²) |
| General, O(1)-sparse | Minimum weight | Õ(k²m + W(kN)^{ω+1}) | O(km + W(kN)³) | Õ(WkN(f^ω + f²k²)) |
| Subset | Existence | O(m^ω) | O((m★)²) | O(f^ω) |
| Subset | Minimum weight | Õ(WkNm^ω) | O(WkN(m★)²) | Õ(WkNf^ω) |

"Here m = |E| in the general setting and m = |E ∪ E★| in the subset setting."

**Formalization Note.**
* As `theorem_7_2`, with error `Cerr k N / |F|` (`Cerr` before the field, depending on the sparsity
  constant `c` only). "O(1)-sparse": for every constant `c`, original and inserted columns
  `c`-sparse.
* A `k`-parity basis (§7.2, p.38) is a set of `kN/2` pairs whose `kN` elements split into `k` bases
  of `M`, the two elements of a pair possibly in different bases (`IsKParityBasis`).
* Hypotheses: `kN` even, and rank `N` (`PairRankFull`) of the original pairs (general) or of all
  listed pairs `E ∪ E★` (subset). -/
theorem theorem_7_3 :
    ∀ c : ℕ, ∃ Cerr : ℝ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ O₃ O₄ : AOracle),
      let ω := OAI.MatrixMultiplication.Arithmetic.omega F
      let q : ℝ := Fintype.card F
      let lg : ℕ → ℝ := fun Z => Real.logb 2 ((Z : ℝ) + 2)
      let prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ :=
        fun _ k L => (∃ S, IsKParityBasis L k S, minKParityWeight L k)
      let admG : (N k W : ℕ) → List (Elem F N) → Prop := fun N k W L =>
        PairRankFull L ∧ Even (k * N) ∧ ∀ x ∈ L, Sparse c x.a ∧ Sparse c x.b ∧ |x.wt| ≤ W
      let insG : (N k W : ℕ) → Elem F N → Prop := fun _ _ W x => Sparse c x.a ∧ Sparse c x.b ∧ |x.wt| ≤ W
      let admS : (N k W : ℕ) → (L : List (Elem F N)) → Finset (Fin L.length) → Finset (Fin L.length) →
        Prop := fun N k _ L _ _ => PairRankFull L ∧ Even (k * N)
      -- General, O(1)-sparse, existence
      O₁.SolvesGeneralOn b admG insG false prob false
        (fun N m k _ _ => C * ((k : ℝ) ^ 2 * m + ((k : ℝ) * N) ^ (ω + τ)))
        (fun N m k _ _ => C * ((k : ℝ) * m + ((k : ℝ) * N) ^ 2))
        (fun _ _ k f _ => C * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2))
        (fun N _ k _ _ => Cerr * k * N / q) ∧
      -- General, O(1)-sparse, minimum weight
      O₂.SolvesGeneralOn b admG insG false prob true
        (fun N m k _ W =>
          C * ((k : ℝ) ^ 2 * m + W * ((k : ℝ) * N) ^ (ω + 1 + τ)) * lg (k + m + W + N) ^ K)
        (fun N m k _ W => C * ((k : ℝ) * m + W * ((k : ℝ) * N) ^ 3))
        (fun N _ k f W =>
          C * (W * k * N * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2)) * lg (W + k + N + f) ^ K)
        (fun N _ k _ _ => Cerr * k * N / q) ∧
      -- Subset, existence
      O₃.SolvesSubsetOn b admS prob false
        (fun _ m _ _ _ _ => C * (m : ℝ) ^ (ω + τ))
        (fun _ _ ms _ _ _ => C * (ms : ℝ) ^ 2)
        (fun _ _ _ _ f _ => C * (f : ℝ) ^ (ω + τ))
        (fun N _ _ k _ _ => Cerr * k * N / q) ∧
      -- Subset, minimum weight
      O₄.SolvesSubsetOn b admS prob true
        (fun N m _ k _ W => C * (W * k * N * (m : ℝ) ^ (ω + τ)) * lg (W + k + N + m) ^ K)
        (fun N _ ms k _ W => C * (W * k * N * (ms : ℝ) ^ 2))
        (fun N _ _ k f W => C * (W * k * N * (f : ℝ) ^ (ω + τ)) * lg (W + k + N + f) ^ K)
        (fun N _ _ k _ _ => Cerr * k * N / q) := by sorry

end MatroidSensOracle.Supplement
