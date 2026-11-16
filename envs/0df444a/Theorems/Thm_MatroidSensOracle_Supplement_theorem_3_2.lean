-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_3_2
-- name    : MatroidSensOracle.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:07:27.553634+00:00
-- url     : https://prove2.me/theorems/4cf0de3e-7edf-4450-a3e0-fc05cda81ef3
-- title:
--   Theorem 3.2 (matroid basis sensitivity): space $O(f\min(m,fN)+N^2)$, query $O(f^\omega+f^2k)$, error $m/|\mathbb F|$
-- statement:
--   Let $\mathbb F$ be a finite field with $\omega=\omega_{\mathbb F}$ its exponent of matrix multiplication, and let $\tau>0$. Let $M$ be the linear matroid of a matrix $A\in\mathbb F^{N\times m}$ of rank $N$ (its elements are the $m$ columns; the original columns may be dense). A query is a set of at most $f$ updates: deletions of original columns and insertions of new columns, each inserted column $k$-sparse (at most $k$ nonzero entries). The question is whether the updated column set still contains a basis, i.e. $N$ linearly independent columns.
--
--   There are a constant $C$ and two oracles on the algebraic RAM over $\mathbb F$ such that:
--
--   1. **Deletions and $k$-sparse insertions.** The oracle stores at most
--   $$C\bigl(f\min(m,fN)+N^2\bigr)$$
--   cells and answers each query in at most $C\,(f^{\omega+\tau}+f^2k)$ steps.
--   2. **Deletions only.** The oracle stores at most $C\,f\min(m,fN)$ cells and answers each query in at most $C\,f^{\omega+\tau}$ steps.
--
--   In both cases each fixed query is answered correctly with probability at least
--   $$1-\frac{m}{|\mathbb F|}.$$
--
--   This is the single-matroid ("1-packing") base case of the paper's determinant framework, and the template for the connectivity oracle of Theorem 4.3.
--
--   **Formalization Note** The matroid is passed in the base mission's element encoding with second column $0$; no preprocessing time is printed, so the preprocessing is only required to halt within some bound depending on the size parameters.
--
--   Differences from the source:
--   - reading: sensitivity oracles for a matroid represented over F (machine unstated) → oracles on the base algebraic RAM over the finite field F (AOracle): time counts all word and field instructions, worst case over the coins; space counts stored word and field cells; the error is over the coins, per fixed query; reason: the machine of the published base milestones Theorems 3.5 and 3.7
--   - encoding: O(x^ω) → C·x^{ω+τ} for every τ > 0, with ω = omega F; reason: ω is an infimum that need not be attained; base convention
--   - reading: no preprocessing time is printed → the preprocessing halts within some bound TP depending only on the size parameters; reason: the theorem bounds only space and query time; finitely many instances share given parameters, so halting is all that is asserted
--   - encoding: a single linear matroid M → a list of base elements whose second column and weight are 0 (IsSingle); only the first columns are read; reason: reuses the base encodings of two-matroid instances; no instance is excluded
--   - encoding: a rank-N matroid on m elements, parameters f, k → N, m, k, f, W ≥ 1, the matroid given by its columns in the base encodings; reason: nondegeneracy, as in the base SolvesGeneral/SolvesSubset; W is a dummy parameter of the encoding for unweighted problems
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 3.2, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_MatroidProblems
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 3.2 (Matroid basis sensitivity).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held
version, sha256 0de50841…), p.17 (PDF p.20): "Let M be a linear matroid of rank N on m elements.
There is a sensitivity oracle taking O(f min(m, fN) + N²) space that decides, for any query of at most
f updates (deletions and k-sparse insertions), whether a basis survives in the updated matroid in
O(f^ω + f²k) time. Moreover, for the setting of only deletions, the oracle space reduces to
O(f min(m, fN)) and query time reduces to O(f^ω). All bounds are randomized with success probability
1 − m/|F|." Setting (§3.1, p.14): the original columns of `A ∈ F^{N×m}` may be dense; each inserted
column is `k`-sparse; the query asks whether the updated column set contains a basis of rank `N`.

**Formalization Note.**
* Machine: the base algebraic RAM over the finite field `F` (`AOracle`); space counts stored cells,
  time all instructions, worst case over the coins; the error is per fixed query.
* `ω = omega F`; `O(x^ω)` is `C x^{ω+τ}` for every `τ > 0`. The error is exactly `m/|F|` (no
  constant), as printed. No preprocessing time is printed: the preprocessing only has to halt, within
  some bound `TP` depending on `(N, m, k, f, W)` (finitely many instances share these parameters).
* The matroid is given by its columns (`IsSingle`: second column and weight `0`, in the base
  encodings); rank `N` (`HasBasisA`) is the theorem's hypothesis. Oracle 1: deletions and insertions
  with `k`-sparse inserted columns (original columns arbitrary). Oracle 2: deletions only.
* The answer (word `0` is `1`) is whether the updated columns contain `N` linearly independent
  columns. All size parameters are at least `1`; `W` is a dummy parameter of the base encoding. -/
theorem theorem_3_2 :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], ∀ τ : ℝ, 0 < τ →
    ∃ (C : ℝ) (b : ℕ) (O₁ O₂ : AOracle) (TP₁ TP₂ : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ),
      let ω := OAI.MatrixMultiplication.Arithmetic.omega F
      let q : ℝ := Fintype.card F
      let prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ := fun _ _ L => (HasBasisA L, ⊤)
      let adm : (N k W : ℕ) → List (Elem F N) → Prop := fun _ _ _ L => HasBasisA L ∧ ∀ x ∈ L, IsSingle x
      -- deletions and k-sparse insertions
      O₁.SolvesGeneralOn b adm (fun _ k _ x => IsSingle x ∧ Sparse k x.a) false prob false TP₁
        (fun N m _ f _ => C * ((f : ℝ) * ((min m (f * N) : ℕ) : ℝ) + (N : ℝ) ^ 2))
        (fun _ _ k f _ => C * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * k))
        (fun _ m _ _ _ => m / q) ∧
      -- deletions only
      O₂.SolvesGeneralOn b adm (fun _ _ _ x => IsSingle x) true prob false TP₂
        (fun N m _ f _ => C * ((f : ℝ) * ((min m (f * N) : ℕ) : ℝ)))
        (fun _ _ _ f _ => C * (f : ℝ) ^ (ω + τ))
        (fun _ m _ _ _ => m / q) := by sorry

end MatroidSensOracle.Supplement
