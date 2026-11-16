-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_11
-- name    : MatroidSensOracle.Supplement.theorem_9_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:25:27.332826+00:00
-- url     : https://prove2.me/theorems/a007769c-0e02-4301-bdff-e60aa00f7481
-- title:
--   Theorem 9.11 (matroid parity subset sensitivity): decision and weighted oracles (corrected: preprocessing includes the $m\,r^{\omega-1}$ cost of forming the parity Laplacian)
-- statement:
--   There is an absolute constant $C_{\mathrm{err}}$ such that the following holds. Let $\mathbb F$ be a finite field, $\omega=\omega_{\mathbb F}$, $\tau>0$, and let $M$ be a linear matroid of rank $r$ over $\mathbb F$ whose elements are grouped into pairs $(a_e,b_e)$ with integer weights in $[-W,W]$. A **parity basis** is a set of $r/2$ pairs whose $r$ columns are linearly independent. Updates are confined to a susceptible set $E_Q$ of $m^\star\ge1$ pairs whose columns are known at preprocessing; a query inserts or deletes at most $f$ of them.
--
--   There are constants $C,K,b$ and two oracles on the algebraic RAM over $\mathbb F$, each answering every fixed query correctly with probability at least $1-C_{\mathrm{err}}\,r/|\mathbb F|$:
--
--   1. **Decision:** preprocessing $C\bigl((m^\star)^2r^{\omega-2+\tau}+r^{\omega+\tau}+m\,r^{\omega-1+\tau}\bigr)$, space $C(m^\star)^2$ cells, query $Cf^{\omega+\tau}$; output whether the updated matroid has a parity basis.
--   2. **Weighted:** preprocessing $\tilde O\bigl(W(m^\star)^2r^{\omega-1}+Wr^{\omega+1}+Wm\,r^{\omega-1}\bigr)$, space $\tilde O(Wr(m^\star)^2)$ cells, query $\tilde O(Wrf^{\omega})$; output the minimum weight of a parity basis (or that none exists).
--
--   Here $m$ is the number of listed pairs ($E\cup E_Q$).
--
--   **Correction.** The printed preprocessing bounds do not depend on $m$, which is false: with $r=2$, $E_Q=\{p\}$, $p=(e_1,e_2)$, all other pairs zero except possibly one hidden pair $(e_1,e_2)$, and the query deleting $p$, the answer depends on the hidden pair, which a preprocessing of $O(1)$ steps cannot find among $m$ positions. The added term is the cost of forming the parity Laplacian $\hat U D_{ext}\hat V^T$ from the $m$ pairs by fast rectangular multiplication.
--
--   Differences from the source:
--   - correction: decision preprocessing O((m★)²r^{ω−2} + r^ω); weighted preprocessing Õ(W(m★)²r^{ω−1} + Wr^{ω+1}) (independent of the number m of pairs) → C·((m★)²r^{ω−2+τ} + r^{ω+τ} + m·r^{ω−1+τ}) and C·(W(m★)²r^{ω−1+τ} + Wr^{ω+1+τ} + W·m·r^{ω−1+τ})·(log₂(Z+2))^K, m = |E ∪ E★|; reason: counterexample: r = 2, E_Q = {p} with p = (e₁, e₂), all other pairs (0, 0) except possibly one hidden pair (e₁, e₂), query deleting p: the answer depends on the hidden pair, which O(1) preprocessing steps cannot locate among m positions, and the query sees only the stored structure; the added term is the cost of forming the parity Laplacian from the m pairs
--   - reading: subset sensitivity oracles for a matroid over F (machine unstated) → oracles on the base algebraic RAM over F (AOracle.SolvesSubsetOn); space in stored cells; reason: the machine of the published base Theorems 3.5 and 3.7
--   - reading: with high probability → error at most C_err·r/|F| per fixed query, C_err absolute and chosen before F; reason: the failure probability the proof inherits from Theorem 3.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, ω = omega F; reason: base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - generalization: E_Q ⊆ E → the base subset setting: the listed ground set E ∪ E★ with E★ = E_Q arbitrary; deletions from E ∩ E★, insertions from E★ ∖ E; reason: E_Q ⊆ E is the special case without insertions
--   - encoding: rank r, pairs with weights in [−W, W] → N = r rows, the 2m pair columns of rank N (PairRankFull), N, k, f, W ≥ 1, |E★| ≥ 1; reason: nondegeneracy as in the base subset setting; k is a dummy parameter
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.11, p.53 (PDF p.56)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_MatroidProblems
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.11 (Matroid Parity Subset Sensitivity Oracle; corrected: preprocessing includes the
`m r^{ω−1}` cost of forming the `r × r` parity Laplacian from the `m` listed pairs).** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.53 (PDF p.56): "Let E_Q ⊆ E be a susceptible
set of m★ pairs. There exist randomized subset sensitivity oracles that, given f updates confined to
pairs in E_Q, answer parity basis queries with high probability:
1. Decision Oracle: Requires O((m★)²r^{ω−2} + r^ω) preprocessing time, O((m★)²) space, and answers
   queries in O(f^ω) time.
2. Weighted Oracle: Requires Õ(W(m★)²r^{ω−1} + Wr^{ω+1}) preprocessing time, Õ(Wr(m★)²) space, and
   answers queries in Õ(Wrf^ω) time."
Setting (§9.5, p.52): a linear matroid of rank `r` with pairs represented by `A, B ∈ F^{r×m}`, pair
weights in `[−W, W]`.

**Formalization Note.**
* The base subset setting on the algebraic RAM (as `theorem_7_2`'s subset rows): the listed pairs are
  `E ∪ E★`, the active set `E`, the susceptible set `E★ = E_Q`; a query deletes `F ⊆ E ∩ E★` and
  inserts `I ⊆ E★ ∖ E`, `|F| + |I| ⩽ f`. The rank `r` is the number `N` of rows, with the hypothesis
  that the listed columns have rank `N` (`PairRankFull`).
* `ω = omega F`; `O(x^ω)`, `O(x^{ω−1})`, `O(x^{ω−2})` are `C x^{ω+τ}`, `C x^{ω−1+τ}`,
  `C x^{ω−2+τ}`; `Õ(X) = C X (log₂(Z + 2))^K`, `Z` the sum of the parameters in `X`; space in cells.
* "With high probability" is the failure probability the proof inherits from Theorem 3.5:
  `Cerr r / |F|` per fixed query, `Cerr` absolute and chosen before the field.
* **Correction (moderation).** As printed, both preprocessing bounds are independent of the number
  `m` of pairs, which is false: take `r = 2`, `E_Q = {p}` with `p = (e₁, e₂)`, every other pair
  `(0, 0)` except possibly one hidden pair `(e₁, e₂)` among `m` positions, and the query deleting `p`.
  The answer (a parity basis survives) is whether the hidden pair is present, the query sees only
  the stored structure and the query, and a preprocessing of `O(1)` steps reads `O(1)` of the `4m`
  input field elements, so for large `m` and `|F|` some instance errs with probability near `1/2`.
  The bounds are corrected by the cost of forming `ℒ_parity = Û D_ext V̂ᵀ` from the `m` listed pairs
  (`r × 2m` times `2m × r`, by fast rectangular multiplication): `+ m r^{ω−1}` (decision) and
  `+ W m r^{ω−1}` (weighted, inside the `Õ`), with `m = |E ∪ E★|` the number of listed pairs. -/
theorem theorem_9_11 :
    ∃ Cerr : ℝ, ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ : AOracle),
      let ω := OAI.MatrixMultiplication.Arithmetic.omega F
      let q : ℝ := Fintype.card F
      let lg : ℕ → ℝ := fun Z => Real.logb 2 ((Z : ℝ) + 2)
      let prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ :=
        fun _ _ L => (∃ S, IsParityBasis L S, minParityWeight L)
      let adm : (N k W : ℕ) → (L : List (Elem F N)) → Finset (Fin L.length) → Finset (Fin L.length) →
        Prop := fun _ _ _ L _ _ => PairRankFull L
      -- Decision oracle
      O₁.SolvesSubsetOn b adm prob false
        (fun r m ms _ _ _ =>
          C * ((ms : ℝ) ^ 2 * (r : ℝ) ^ (ω - 2 + τ) + (r : ℝ) ^ (ω + τ) + m * (r : ℝ) ^ (ω - 1 + τ)))
        (fun _ _ ms _ _ _ => C * (ms : ℝ) ^ 2)
        (fun _ _ _ _ f _ => C * (f : ℝ) ^ (ω + τ))
        (fun r _ _ _ _ _ => Cerr * r / q) ∧
      -- Weighted oracle
      O₂.SolvesSubsetOn b adm prob true
        (fun r m ms _ _ W =>
          C * (W * (ms : ℝ) ^ 2 * (r : ℝ) ^ (ω - 1 + τ) + W * (r : ℝ) ^ (ω + 1 + τ) +
            W * m * (r : ℝ) ^ (ω - 1 + τ)) * lg (W + ms + r + m) ^ K)
        (fun r _ ms _ _ W => C * (W * r * (ms : ℝ) ^ 2) * lg (W + r + ms) ^ K)
        (fun r _ _ _ f W => C * (W * r * (f : ℝ) ^ (ω + τ)) * lg (W + r + f) ^ K)
        (fun r _ _ _ _ _ => Cerr * r / q) := by sorry

end MatroidSensOracle.Supplement
