-- Prove2me | Theorems.Thm_MatroidSensOracle_theorem_3_5
-- name    : MatroidSensOracle.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:58.195194+00:00
-- url     : https://prove2.me/theorems/62753e02-aa50-49fc-bc84-0f3d5ac67a4a
-- title:
--   Theorem 3.5 (Common-basis sensitivity), all four rows of Table 8
-- statement:
--   There is an absolute constant $C_{\mathrm{err}}$ such that the following holds. Let $\mathbb F$ be a finite field, $\omega=\omega_{\mathbb F}$, and $\tau>0$. There are constants $C,K,b$ and four oracles on the algebraic RAM over $\mathbb F$ answering, for updated matroids after at most $f$ element insertions and deletions, whether they have a common basis of size $N$ (and, weighted, its minimum weight), each fixed query wrongly with probability at most $C_{\mathrm{err}}N/|\mathbb F|$. Writing $\ell=\log_2(N+m+k+f+W+2)$:
--
--   1. General setting, $k$-sparse columns, existence: preprocessing $C(k^2m+N^{\omega+\tau})$, space $C(km+N^2)$, query $C(f^{\omega+\tau}+f^2k^2)$.
--   2. General setting, $k$-sparse, minimum weight: preprocessing $C(k^2m+WN^{\omega+1+\tau})\ell^K$, space $C(km+WN^3)$, query $C\,NW(f^{\omega+\tau}+f^2k^2)\,\ell^K$.
--   3. Subset setting, existence: preprocessing $C\,m^{\omega+\tau}$, space $C(m^\star)^2$, query $C f^{\omega+\tau}$.
--   4. Subset setting, minimum weight: preprocessing $C\,NWm^{\omega+\tau}\ell^K$, space $C\,NW(m^\star)^2$, query $C\,NWf^{\omega+\tau}\ell^K$.
--
--   Here $m=|E|$ in the general setting and $m=|E\cup E^\star|$ in the subset setting; times are worst case and space counts stored cells. Applied to $k$-fold union representations it gives Theorem 3.7.
--
--   Differences from the source:
--   - reading: sensitivity oracles over F with preprocessing time, space, query time (machine unstated) → oracles on the algebraic RAM over the finite field F; time counts all instructions, worst case over coins; space counts stored word and field cells; error per fixed query over the coins of preprocessing and query; reason: the paper's costs are field operations and stored field elements (p.13, Lemma 2.2); worst-case time and per-query error are the strong readings
--   - encoding: O(x^ω), ω over F → C x^{ω+τ} for every τ > 0, ω = omega F; reason: ω is an infimum over admissible exponents
--   - encoding: Õ(·) → a factor (log₂(N + m + k + f + W + 2))^K; reason: polylog of the instance size
--   - reading: O(·) bounds; error O(N/|F|) → one constant C (it and the programs may depend on F and τ) for the time and space bounds of all four rows; an absolute constant Cerr, chosen before F, in the error Cerr·N/|F|; reason: the field size |F| appears only in the error bound, and an error constant depending on F could absorb |F| and make the error clause vacuous; ω = omega F itself depends on F
--   - encoding: N, m, k, f, W, m★ → all at least 1; reason: the printed bounds vanish at 0 and no run meets them; this excludes only undefined cases
--   - encoding: input matroids given by representations; weights in [−W, W] → the input is a list of elements (two columns and a weight in [−W, W]), sparse columns as lists of nonzero entries, dense columns in the subset setting; weights are given also for the existence rows; reason: input layout; existence does not depend on the weights
--   - reading: element insertions and deletions; updates confined to E★ → general: delete any set of positions, insert new elements with sparse columns and weights; subset: delete F ⊆ E ∩ E★, insert I ⊆ E★ \ E, |F| + |I| ≤ f; reason: the paper's two settings (§3.2, pp.17–18)
--   - generalization: M1, M2 rank-N matroids → no rank hypothesis on the input; the oracle reports none when no common basis exists; reason: the paper's handling of a non-invertible Laplacian (p.19) covers this; rank-N inputs are a special case
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 3.5 and Table 8, pp.19–20 (PDF pp.22–23); settings §3.2, pp.17–19

import Mathlib
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle

/-- **Theorem 3.5 (Common-basis sensitivity), with Table 8.** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), pp.19–20 (PDF pp.22–23): "Let M1 and M2 be rank-N
linear matroids represented over F on a common ground set E. There exists following sensitivity
oracles that given at most f element insertions and deletions, decides whether the updated matroids
have a common basis of size N and, for integer weights in [−W, W], report its minimum possible weight
if one exists. The answer to each query is correct with probability at least 1 − O(N/|F|)."

| Setting | Objective | Preprocessing time | Space | Query time |
|---|---|---|---|---|
| General, k-sparse | Existence | O(k²m + N^ω) | O(km + N²) | O(f^ω + f²k²) |
| General, k-sparse | Minimum weight | Õ(k²m + WN^{ω+1}) | O(km + WN³) | Õ(NW(f^ω + f²k²)) |
| Subset | Existence | O(m^ω) | O((m★)²) | O(f^ω) |
| Subset | Minimum weight | Õ(NWm^ω) | O(NW(m★)²) | Õ(NWf^ω) |

"Here m = |E| in the general setting and m = |E ∪ E★| in the subset setting."

**Formalization Note.**
* Machine and oracle semantics: the algebraic RAM over the finite field `F` (`AOracle`); space counts
  stored word and field cells, time counts all instructions, worst case over all coins; the error is
  per fixed query, over the coins of preprocessing and query.
* `ω = omega F`; `O(x^ω)` is `C x^{ω+τ}` for every `τ > 0`. `Õ` hides
  `(log₂(N + m + k + f + W + 2))^K`. The error bound is `Cerr N / |F|` with one absolute
  constant `Cerr`, chosen before the field (a constant depending on `F` could absorb `|F|` and make
  the error clause vacuous). One constant `C` serves the time and space bounds of every row; it and
  the programs may depend on `F` and `τ` (as `ω = omega F` does), not on `N, m, k, f, W`.
* General setting: original and inserted columns `k`-sparse in both representations
  (`SolvesGeneral` with sparsity `k`). Subset setting: dense columns, ground set `E ∪ E★`.
* "Existence" asks for a common basis of size `N` of the updated matroids (`HasCommonBasis`); the
  weighted rows also return its minimum weight (`minCommonBasisWeight`). Both are asked of every
  instance, including updated matroids of rank `< N` (then the answer is "none").
* Rank `N` of the input matroids is not assumed (the oracle reports "none" when there is no common
  basis); all size parameters are at least `1`. -/
theorem theorem_3_5 :
    ∃ Cerr : ℝ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ O₃ O₄ : AOracle),
      let ω := OAI.MatrixMultiplication.Arithmetic.omega F
      let q : ℝ := Fintype.card F
      let prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ :=
        fun _ _ L => (HasCommonBasis L, minCommonBasisWeight L)
      let lg : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ := fun N m k f W => Real.logb 2 ((N + m + k + f + W + 2 : ℕ) : ℝ)
      -- General, k-sparse, existence
      O₁.SolvesGeneral b id prob false
        (fun N m k _ _ => C * ((k : ℝ) ^ 2 * m + (N : ℝ) ^ (ω + τ)))
        (fun N m k _ _ => C * ((k : ℝ) * m + (N : ℝ) ^ 2))
        (fun _ _ k f _ => C * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2))
        (fun N _ _ _ _ => Cerr * N / q) ∧
      -- General, k-sparse, minimum weight
      O₂.SolvesGeneral b id prob true
        (fun N m k f W => C * ((k : ℝ) ^ 2 * m + W * (N : ℝ) ^ (ω + 1 + τ)) * lg N m k f W ^ K)
        (fun N m k _ W => C * ((k : ℝ) * m + W * (N : ℝ) ^ 3))
        (fun N m k f W => C * (N * W * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2)) * lg N m k f W ^ K)
        (fun N _ _ _ _ => Cerr * N / q) ∧
      -- Subset, existence
      O₃.SolvesSubset b prob false
        (fun _ m _ _ _ _ => C * (m : ℝ) ^ (ω + τ))
        (fun _ _ ms _ _ _ => C * (ms : ℝ) ^ 2)
        (fun _ _ _ _ f _ => C * (f : ℝ) ^ (ω + τ))
        (fun N _ _ _ _ _ => Cerr * N / q) ∧
      -- Subset, minimum weight
      O₄.SolvesSubset b prob true
        (fun N m _ k f W => C * (N * W * (m : ℝ) ^ (ω + τ)) * lg N m k f W ^ K)
        (fun N _ ms _ _ W => C * (N * W * (ms : ℝ) ^ 2))
        (fun N m _ k f W => C * (N * W * (f : ℝ) ^ (ω + τ)) * lg N m k f W ^ K)
        (fun N _ _ _ _ _ => Cerr * N / q) := by sorry

end MatroidSensOracle
