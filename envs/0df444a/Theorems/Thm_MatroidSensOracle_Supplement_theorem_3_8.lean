-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_3_8
-- name    : MatroidSensOracle.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:08:09.636568+00:00
-- url     : https://prove2.me/theorems/ae7274be-a987-4d9d-90cd-64c5717ec90f
-- title:
--   Theorem 3.8 ($k$-packing sensitivity), both rows of Table 10
-- statement:
--   Let $c$ be a sparsity constant. There is a constant $C_{\mathrm{err}}$ (depending on $c$ only) such that the following holds. Let $\mathbb F$ be a finite field, $\omega=\omega_{\mathbb F}$, and $\tau>0$. Let $M$ be a rank-$N$ linear matroid on $m$ elements represented over $\mathbb F$, and let $k\ge 1$. A **$k$-packing** is a set of elements that splits into $k$ pairwise disjoint bases of $M$. Queries consist of at most $f$ element deletions and insertions, and ask whether the updated matroid has a $k$-packing.
--
--   There are constants $C$, $b$ and two oracles on the algebraic RAM over $\mathbb F$, each answering every fixed query correctly with probability at least $1-C_{\mathrm{err}}\,kN/|\mathbb F|$:
--
--   1. **Deletions only:** preprocessing $C\,m^{\omega+\tau}$, space $C\,f\min\{m,fkN\}$ cells, query $C\,f^{\omega+\tau}$.
--   2. **Insertions and deletions** (inserted columns $c$-sparse, original columns arbitrary): preprocessing $C\,m^{\omega+\tau}$, space
--   $$C\bigl(f\min\{m,fkN\}+(kN)^2\bigr)$$
--   cells, query $C\,(f^{\omega+\tau}+f^2k)$.
--
--   Packings of bases of one matroid underlie the spanning-tree and arborescence applications of §6.
--
--   **Formalization Note** The mixed row's bounds come from applying the single-matroid oracle of Theorem 3.2 to the union representation $A^{\vee k}$ (p.21), so only the inserted columns are assumed $O(1)$-sparse; the original columns may be dense.
--
--   Differences from the source:
--   - reading: sensitivity oracles for a matroid represented over F (machine unstated) → oracles on the base algebraic RAM over the finite field F (AOracle): time counts all word and field instructions, worst case over the coins; space counts stored word and field cells; the error is over the coins, per fixed query; reason: the machine of the published base milestones Theorems 3.5 and 3.7
--   - encoding: O(x^ω) → C·x^{ω+τ} for every τ > 0, with ω = omega F; reason: ω is an infimum that need not be attained; base convention
--   - reading: insertions and deletions row (no sparsity printed in Theorem 3.8) → inserted columns c-sparse, for every constant c (constants depending on c); original columns arbitrary; reason: the row's bounds come from applying the single-matroid oracle of Theorem 3.2 to A^∨k (p.21), which needs only the inserted columns sparse; a dense inserted column cannot be read in O(f^ω + f²k) time
--   - encoding: a single linear matroid M → a list of base elements whose second column and weight are 0 (IsSingle); only the first columns are read; reason: reuses the base encodings of two-matroid instances; no instance is excluded
--   - encoding: a rank-N matroid on m elements, parameters f, k → N, m, k, f, W ≥ 1, the matroid given by its columns in the base encodings; reason: nondegeneracy, as in the base SolvesGeneral/SolvesSubset; W is a dummy parameter of the encoding for unweighted problems
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 3.8, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_MatroidProblems
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 3.8 (k-packing sensitivity), with Table 10.** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.21 (PDF p.24): "Let M be a rank-N linear matroid
on m elements represented over F. There exists following sensitivity oracles that given at most f
element insertions and deletions, decides whether the updated matroid haa a k-packing. Each fixed
query is answered correctly with probability at least 1 − O(kN/|F|)."

| Updates | Preprocessing time | Space | Query time |
|---|---|---|---|
| Deletions only | O(m^ω) | O(f min{m, fkN}) | O(f^ω) |
| Insertions and deletions | O(m^ω) | O(f min{m, fkN} + (kN)²) | O(f^ω + f²k) |

**Formalization Note.**
* Machine, semantics, `ω = omega F`, `O(x^ω) = C x^{ω+τ}` as in the base `theorem_3_7`. The error is
  `Cerr k N / |F|` with `Cerr` chosen before the field.
* A `k`-packing is a set of elements splitting into `k` pairwise disjoint bases (`N` independent
  columns each) of the single matroid (`HasKPackingA`); the matroid is given by its columns
  (`IsSingle`), of rank `N` (hypothesis).
* Row 1: deletions only, original columns arbitrary. Row 2: insertions and deletions. Its bounds
  come from applying the single-matroid oracle of Theorem 3.2 to `A^{∨k}` (p.21: "For unweighted
  k-packing, we can additionally apply the single-matroid oracle of Theorem 3.2 to A^{∨k}"), which
  allows dense original columns and needs sparse inserted columns: for every constant `c`, inserted
  columns `c`-sparse ("O(1)-sparse", Table 9), original columns arbitrary; constants and programs
  depend on `c`. -/
theorem theorem_3_8 :
    ∀ c : ℕ, ∃ Cerr : ℝ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (b : ℕ) (O₁ O₂ : AOracle),
      let ω := OAI.MatrixMultiplication.Arithmetic.omega F
      let q : ℝ := Fintype.card F
      let prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ := fun _ k L => (HasKPackingA L k, ⊤)
      -- Deletions only
      O₁.SolvesGeneralOn b (fun _ _ _ L => HasBasisA L ∧ ∀ x ∈ L, IsSingle x)
        (fun _ _ _ x => IsSingle x) true prob false
        (fun _ m _ _ _ => C * (m : ℝ) ^ (ω + τ))
        (fun N m k f _ => C * ((f : ℝ) * ((min m (f * k * N) : ℕ) : ℝ)))
        (fun _ _ _ f _ => C * (f : ℝ) ^ (ω + τ))
        (fun N _ k _ _ => Cerr * k * N / q) ∧
      -- Insertions and deletions (inserted columns c-sparse, original columns arbitrary)
      O₂.SolvesGeneralOn b (fun _ _ _ L => HasBasisA L ∧ ∀ x ∈ L, IsSingle x)
        (fun _ _ _ x => IsSingle x ∧ Sparse c x.a) false prob false
        (fun _ m _ _ _ => C * (m : ℝ) ^ (ω + τ))
        (fun N m k f _ => C * ((f : ℝ) * ((min m (f * k * N) : ℕ) : ℝ) + ((k : ℝ) * N) ^ 2))
        (fun _ _ k f _ => C * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * k))
        (fun N _ k _ _ => Cerr * k * N / q) := by sorry

end MatroidSensOracle.Supplement
