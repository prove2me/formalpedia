-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_3_10
-- name    : MatroidSensOracle.Supplement.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:08:54.758329+00:00
-- url     : https://prove2.me/theorems/327a2e99-72d8-4c92-95bc-1544a73a0f77
-- title:
--   Theorem 3.10 ($k$-covering sensitivity), all three rows of Table 11
-- statement:
--   Let $c$ be a sparsity constant. There is a constant $C_{\mathrm{err}}$ (depending on $c$ only) such that the following holds. Let $\mathbb F$ be a finite field, $\omega=\omega_{\mathbb F}$, $\tau>0$, and let $M$ be a rank-$N$ linear matroid on $m\le kN$ elements represented over $\mathbb F$. The ground set is **$k$-coverable** if it can be partitioned into $k$ independent sets of $M$. Queries consist of at most $f$ element insertions and deletions and ask whether the updated ground set is $k$-coverable.
--
--   There are constants $C$, $b$ and three oracles on the algebraic RAM over $\mathbb F$, each answering every fixed query correctly with probability at least $1-C_{\mathrm{err}}\,kN/|\mathbb F|$:
--
--   1. **General, via common basis** (columns $c$-sparse): preprocessing $C(kN)^{\omega+\tau}$, space $C\,k^2N^2$, query $C(f^{\omega+\tau}+f^2k^2)$.
--   2. **Subset, via common basis** (updates confined to a set $E^\star$ of $m^\star$ elements whose columns are known at preprocessing): preprocessing $C(kN+m^\star)^{\omega+\tau}$, space $C(m^\star)^2$, query $C f^{\omega+\tau}$.
--   3. **General, via single-matroid basis** (columns $c$-sparse): preprocessing $C(kN)^{\omega+\tau}$, space $C(fkN+k^2N^2)$, query $C(f^{\omega+\tau}+f^2k)$.
--
--   Space is counted in stored cells. The covering oracle is the engine of the arboricity oracles (Theorems 6.10 and 9.10).
--
--   **Formalization Note** In the subset row the hypothesis $m\le kN$ is read on the active ground set $E$ (the matroid $M$); the susceptible elements outside $E$ are listed with it, as in the base subset encoding.
--
--   Differences from the source:
--   - reading: sensitivity oracles for a matroid represented over F (machine unstated) → oracles on the base algebraic RAM over the finite field F (AOracle): time counts all word and field instructions, worst case over the coins; space counts stored word and field cells; the error is over the coins, per fixed query; reason: the machine of the published base milestones Theorems 3.5 and 3.7
--   - encoding: O(x^ω) → C·x^{ω+τ} for every τ > 0, with ω = omega F; reason: ω is an infimum that need not be attained; base convention
--   - reading: m ⩽ kN in the subset setting → |E| ≤ kN for the active set E; the listed ground set E ∪ E★ may be larger; reason: M is the matroid on E; E★ holds the potential insertions
--   - encoding: O(1)-sparse columns (general rows) → for every constant c, columns c-sparse; constants depend on c; reason: the printed setting of Table 11
--   - encoding: a single linear matroid M → a list of base elements whose second column and weight are 0 (IsSingle); only the first columns are read; reason: reuses the base encodings of two-matroid instances; no instance is excluded
--   - encoding: a rank-N matroid on m elements, parameters f, k → N, m, k, f, W ≥ 1, the matroid given by its columns in the base encodings; reason: nondegeneracy, as in the base SolvesGeneral/SolvesSubset; W is a dummy parameter of the encoding for unweighted problems
--   - generalization: subset row: M is a rank-N matroid on the active ground set E → the columns of all listed elements E ∪ E★ have rank N (HasBasisA of the whole list); reason: rank N of E implies rank N of E ∪ E★ (both have N rows), so every instance of the source is covered
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 3.10, p.23 (PDF p.26)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_MatroidProblems
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 3.10 (k-covering sensitivity), with Table 11.** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.23 (PDF p.26): "Let M be a rank-N linear
matroid on m ⩽ kN elements, represented over F. There are randomized sensitivity oracles that, given
at most f element insertions and deletions, decide whether the updated ground set can be partitioned
into k independent sets of M. The preprocessing time, space, and query time are given in Table 11.
Each fixed query is answered correctly with probability at least 1 − O(kN/|F|)."

| Setting and oracle | Preprocessing time | Space | Query time |
|---|---|---|---|
| General, via common basis | O((kN)^ω) | O(k²N²) | O(f^ω + f²k²) |
| Subset, via common basis | O((kN + m★)^ω) | O((m★)²) | O(f^ω) |
| General, via single-matroid basis | O((kN)^ω) | O(fkN + k²N²) | O(f^ω + f²k) |

"In the general setting, the original and inserted columns of the base representation are
O(1)-sparse. In the subset setting, updates are confined to a prescribed set of m★ elements whose
representation columns are known during preprocessing."

**Formalization Note.**
* Machine, semantics, `ω = omega F`, `O(x^ω) = C x^{ω+τ}`, error `Cerr k N / |F|` with `Cerr` before
  the field, as in the base `theorem_3_7`. "O(1)-sparse": for every constant `c`, columns
  `c`-sparse, constants and programs depending on `c`.
* `KCoverable L k`: the whole updated ground set splits into `k` independent sets. The matroid is
  given by its columns (`IsSingle`).
* Hypotheses: general rows: rank `N` of the original columns and `m = |E| ⩽ kN`; subset row: the
  active set has `|E| ⩽ kN` and the columns of `E ∪ E★` (all listed elements) have rank `N`. -/
theorem theorem_3_10 :
    ∀ c : ℕ, ∃ Cerr : ℝ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (b : ℕ) (O₁ O₂ O₃ : AOracle),
      let ω := OAI.MatrixMultiplication.Arithmetic.omega F
      let q : ℝ := Fintype.card F
      let prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ := fun _ k L => (KCoverable L k, ⊤)
      let admG : (N k W : ℕ) → List (Elem F N) → Prop := fun N k _ L =>
        HasBasisA L ∧ L.length ≤ k * N ∧ ∀ x ∈ L, IsSingle x ∧ Sparse c x.a
      let insG : (N k W : ℕ) → Elem F N → Prop := fun _ _ _ x => IsSingle x ∧ Sparse c x.a
      -- General, via common basis
      O₁.SolvesGeneralOn b admG insG false prob false
        (fun N _ k _ _ => C * ((k : ℝ) * N) ^ (ω + τ))
        (fun N _ k _ _ => C * ((k : ℝ) ^ 2 * (N : ℝ) ^ 2))
        (fun _ _ k f _ => C * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2))
        (fun N _ k _ _ => Cerr * k * N / q) ∧
      -- Subset, via common basis
      O₂.SolvesSubsetOn b
        (fun N k _ L Eact _ => HasBasisA L ∧ Eact.card ≤ k * N ∧ ∀ x ∈ L, IsSingle x) prob false
        (fun N _ ms k _ _ => C * ((k : ℝ) * N + ms) ^ (ω + τ))
        (fun _ _ ms _ _ _ => C * (ms : ℝ) ^ 2)
        (fun _ _ _ _ f _ => C * (f : ℝ) ^ (ω + τ))
        (fun N _ _ k _ _ => Cerr * k * N / q) ∧
      -- General, via single-matroid basis
      O₃.SolvesGeneralOn b admG insG false prob false
        (fun N _ k _ _ => C * ((k : ℝ) * N) ^ (ω + τ))
        (fun N _ k f _ => C * ((f : ℝ) * k * N + (k : ℝ) ^ 2 * (N : ℝ) ^ 2))
        (fun _ _ k f _ => C * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * k))
        (fun N _ k _ _ => Cerr * k * N / q) := by sorry

end MatroidSensOracle.Supplement
