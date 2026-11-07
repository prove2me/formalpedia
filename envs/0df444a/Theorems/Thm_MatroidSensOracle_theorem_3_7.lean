-- Prove2me | Theorems.Thm_MatroidSensOracle_theorem_3_7
-- name    : MatroidSensOracle.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:20.330889+00:00
-- url     : https://prove2.me/theorems/4e589404-fc94-443c-9345-a78b76e446a1
-- title:
--   Theorem 3.7 ($k$-intersection-packing sensitivity), all four rows of Table 9
-- statement:
--   Let $c$ be a sparsity constant. There is a constant $C_{\mathrm{err}}$ (depending on $c$ only) such that the following holds. Let $\mathbb F$ be a finite field, $\omega=\omega_{\mathbb F}$, and $\tau>0$. There are constants $C,K,b$ and four oracles on the algebraic RAM over $\mathbb F$ answering, for updated matroids after at most $f$ element insertions and deletions, whether they have a $k$-intersection-packing (and, weighted, its minimum weight), each fixed query wrongly with probability at most $C_{\mathrm{err}}kN/|\mathbb F|$. Writing $\ell=\log_2(N+m+k+f+W+2)$:
--
--   1. General setting, $c$-sparse columns, existence: preprocessing $C(k^2m+(kN)^{\omega+\tau})$, space $C(km+(kN)^2)$, query $C(f^{\omega+\tau}+f^2k^2)$.
--   2. General, minimum weight: preprocessing $C(k^2m+W(kN)^3)\ell^K$, space $C(km+W(kN)^3)$, query $C\,WkN(f^{\omega+\tau}+f^2k^2)\,\ell^K$.
--   3. Subset, existence: preprocessing $C\,m^{\omega+\tau}$, space $C(m^\star)^2$, query $Cf^{\omega+\tau}$.
--   4. Subset, minimum weight: preprocessing $C\,WkNm^{\omega+\tau}\ell^K$, space $C\,WkN(m^\star)^2$, query $C\,WkNf^{\omega+\tau}\ell^K$.
--
--   Applied to the partition matroids of §5.1 it yields the bounded-flow oracles behind Theorem 5.5.
--
--   Differences from the source:
--   - reading: sensitivity oracles over F with preprocessing time, space, query time (machine unstated) → oracles on the algebraic RAM over the finite field F; time counts all instructions, worst case over coins; space counts stored word and field cells; error per fixed query over the coins of preprocessing and query; reason: the paper's costs are field operations and stored field elements (p.13, Lemma 2.2); worst-case time and per-query error are the strong readings
--   - encoding: O(x^ω), ω over F → C x^{ω+τ} for every τ > 0, ω = omega F; reason: ω is an infimum over admissible exponents
--   - encoding: Õ(·) → a factor (log₂(N + m + k + f + W + 2))^K; reason: polylog of the instance size
--   - reading: O(·) bounds; error O(kN/|F|) → one constant C (it and the programs may depend on F, c and τ) for the time and space bounds of all four rows; a constant Cerr depending on c only, chosen before F, in the error Cerr·k·N/|F|; reason: the field size |F| appears only in the error bound, and an error constant depending on F could absorb |F| and make the error clause vacuous; ω = omega F itself depends on F
--   - encoding: N, m, k, f, W, m★ → all at least 1; reason: the printed bounds vanish at 0 and no run meets them; this excludes only undefined cases
--   - encoding: input matroids given by representations; weights in [−W, W] → the input is a list of elements (two columns and a weight in [−W, W]), sparse columns as lists of nonzero entries, dense columns in the subset setting; weights are given also for the existence rows; reason: input layout; existence does not depend on the weights
--   - reading: element insertions and deletions; updates confined to E★ → general: delete any set of positions, insert new elements with sparse columns and weights; subset: delete F ⊆ E ∩ E★, insert I ⊆ E★ \ E, |F| + |I| ≤ f; reason: the paper's two settings (§3.2, pp.17–18)
--   - reading: General, O(1)-sparse → for every constant c, original and inserted columns c-sparse, with constants and programs depending on c; reason: the usual meaning of O(1); the fold count k stays a free parameter
--   - reading: a k-intersection-packing; its minimum possible weight → a set splitting into k disjoint N-sets independent in the first representation and, possibly differently, into k such sets in the second; the minimum of its weight; reason: the definition on p.20; bases of a rank-N matroid have N elements
--   - generalization: M1, M2 rank-N matroids → no rank hypothesis on the input; the oracle reports none when no packing exists; reason: the paper's rank-deficit handling (p.21) covers this; rank-N inputs are a special case
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 3.7 and Table 9, p.21 (PDF p.24); settings §3.2–3.3, pp.17–21

import Mathlib
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle

/-- **Theorem 3.7 (k-intersection-packing sensitivity), with Table 9.** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.21 (PDF p.24): "Let M1 and M2 be rank-N linear
matroids represented over F on a common ground set E. There exists following sensitivity oracles that
given at most f element insertions and deletions, decides whether the updated matroids have a
k-intersection-packing and, for integer weights in [−W, W], report its minimum possible weight if one
exists. Each fixed query is answered correctly with probability at least 1 − O(kN/|F|)."

| Setting | Objective | Preprocessing time | Space | Query time |
|---|---|---|---|---|
| General, O(1)-sparse | Existence | O(k²m + (kN)^ω) | O(km + (kN)²) | O(f^ω + f²k²) |
| General, O(1)-sparse | Minimum weight | Õ(k²m + W(kN)³) | O(km + W(kN)³) | Õ(WkN(f^ω + f²k²)) |
| Subset | Existence | O(m^ω) | O((m★)²) | O(f^ω) |
| Subset | Minimum weight | Õ(WkNm^ω) | O(WkN(m★)²) | Õ(WkNf^ω) |

"Here m = |E| in the general setting and m = |E ∪ E★| in the subset setting."

**Formalization Note.**
* Same machine, oracle semantics and conventions as `theorem_3_5`; `ω = omega F`, `O(x^ω)` is
  `C x^{ω+τ}` for every `τ > 0`, `Õ` hides `(log₂(N + m + k + f + W + 2))^K`, error `Cerr k N / |F|`
  with `Cerr` chosen before the field (it may depend on the sparsity constant `c` only).
* `k` is the number of bases (a parameter of the instance, `k ≥ 1`). "O(1)-sparse" means: for every
  constant `c`, with original and inserted columns `c`-sparse, there are constants `C, K, b` and
  programs (depending on `F`, `c`, `τ`).
* A `k`-intersection-packing is a set of `kN` elements that splits into `k` bases of each matroid
  (`HasKPacking`, the two splittings may differ); the weighted rows return the minimum weight of such
  a set (`minKPackingWeight`). -/
theorem theorem_3_7 :
    ∀ c : ℕ, ∃ Cerr : ℝ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ O₃ O₄ : AOracle),
      let ω := OAI.MatrixMultiplication.Arithmetic.omega F
      let q : ℝ := Fintype.card F
      let prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ :=
        fun _ k L => (HasKPacking L k, minKPackingWeight L k)
      let lg : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ := fun N m k f W => Real.logb 2 ((N + m + k + f + W + 2 : ℕ) : ℝ)
      -- General, O(1)-sparse, existence
      O₁.SolvesGeneral b (fun _ => c) prob false
        (fun N m k _ _ => C * ((k : ℝ) ^ 2 * m + ((k : ℝ) * N) ^ (ω + τ)))
        (fun N m k _ _ => C * ((k : ℝ) * m + ((k : ℝ) * N) ^ 2))
        (fun _ _ k f _ => C * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2))
        (fun N _ k _ _ => Cerr * k * N / q) ∧
      -- General, O(1)-sparse, minimum weight
      O₂.SolvesGeneral b (fun _ => c) prob true
        (fun N m k f W => C * ((k : ℝ) ^ 2 * m + W * ((k : ℝ) * N) ^ 3) * lg N m k f W ^ K)
        (fun N m k _ W => C * ((k : ℝ) * m + W * ((k : ℝ) * N) ^ 3))
        (fun N m k f W =>
          C * (W * k * N * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2)) * lg N m k f W ^ K)
        (fun N _ k _ _ => Cerr * k * N / q) ∧
      -- Subset, existence
      O₃.SolvesSubset b prob false
        (fun _ m _ _ _ _ => C * (m : ℝ) ^ (ω + τ))
        (fun _ _ ms _ _ _ => C * (ms : ℝ) ^ 2)
        (fun _ _ _ _ f _ => C * (f : ℝ) ^ (ω + τ))
        (fun N _ _ k _ _ => Cerr * k * N / q) ∧
      -- Subset, minimum weight
      O₄.SolvesSubset b prob true
        (fun N m _ k f W => C * (W * k * N * (m : ℝ) ^ (ω + τ)) * lg N m k f W ^ K)
        (fun N _ ms k _ W => C * (W * k * N * (ms : ℝ) ^ 2))
        (fun N m _ k f W => C * (W * k * N * (f : ℝ) ^ (ω + τ)) * lg N m k f W ^ K)
        (fun N _ _ k _ _ => Cerr * k * N / q) := by sorry

end MatroidSensOracle
