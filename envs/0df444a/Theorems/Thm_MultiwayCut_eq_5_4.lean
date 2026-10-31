-- Prove2me | Theorems.Thm_MultiwayCut_eq_5_4
-- name    : MultiwayCut.eq_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:49.272499+00:00
-- url     : https://prove2.me/theorems/e00b4049-d696-4c8c-b1e5-c992ec1ffa1a
-- title:
--   (5.4) — $S_1,\dots,S_4$, $T_5=5/18$ and $S_\ell/\ell=1/(9\ell)+5/9\le7/12$ for $\ell\ge4$
-- statement:
--   For the matrix $A$ of (5.3) let $S_\ell=\sum_{i=1}^\ell\sum_{j=1}^\ell a_{ij}$ and $T_5=\sum_{i=1}^3a_{i5}$. Then
--   1. $S_1=1$, $S_2=\frac{40}{27}$, $S_3=\frac{37}{18}$, $S_4=\frac73$ (when $k\ge4$);
--   2. $\sum_{i=1}^3 a_{ij}=\frac5{18}$ for every $j\ge5$, so $T_5=\frac5{18}$;
--   3. for every $4\le\ell\le k$, $S_\ell=S_4+2(\ell-4)T_5$ and
--   $$\frac1\ell S_\ell=\frac1\ell(S_4-8T_5)+2T_5=\frac1{9\ell}+\frac59\le\frac7{12}.\tag{5.4}$$
--
--   These identities drive the case analysis in the proof of Lemma 5.4.
--
--   Differences from the source:
--   - encoding: the paper's coordinates and terminals $1,\dots,k$, $1/\ell$ → `Fin k` from $0$, $1/(\ell+1)$; reason: Lean convention; the same statement after the index shift
--   - reading: the matrix (5.3) printed with "…" for a general $k$ → `A53 k` for every $k\ge1$, defined by the entry formula (the top-left $k\times k$ block of the printed pattern); reason: the paper never restricts $k$; this is the only matrix consistent with the printed pattern
--   - encoding: the chain $\frac1\ell S_\ell=\dots=\dots\le\frac7{12}$ with $T_5$ and $S_4$ as symbols → one conjunct per link, with $S_4=\frac73$ and $T_5=\frac5{18}$ substituted; reason: the values are clauses 1 and 2 of the same item
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, proof of Lemma 5.4, definitions of T_5 and S_ℓ and display (5.4), p.8

import Mathlib
import Definitions.Def_MultiwayCut_A53

namespace MultiwayCut

/-- **The sums `S_ℓ`, `T₅` and (5.4)**, Buchbinder, Schwartz & Weizman, *Simplex Transformations
and the Multiway Cut Problem*, manuscript of Nov. 1, 2016, proof of Lemma 5.4, p.8: for the
matrix `A` of (5.3), with `S_ℓ = Σ_{i=1}^ℓ Σ_{j=1}^ℓ a_ij` and `T₅ = Σ_{i=1}^3 a_{i5}`:
`S₁ = 1`, `S₂ = 40/27`, `S₃ = 37/18`, `S₄ = 7/3`; `T₅ = Σ_{i=1}^3 a_ij = 5/18` for every
`j ≥ 5`; `S_ℓ = S₄ + 2(ℓ − 4)T₅` for all `ℓ ≥ 4`; and therefore, for all `ℓ ≥ 4`,
(5.4) `(1/ℓ) S_ℓ = (1/ℓ)(S₄ − 8T₅) + 2T₅ = 1/(9ℓ) + 5/9 ≤ 7/12`.

**Formalization Note.** 0-based: `S_ℓ` is the sum over `Finset.Iic ⟨ℓ − 1⟩ × Finset.Iic ⟨ℓ − 1⟩`.
`S₁, …, S₄` need `k ≥ 4`, `T₅` needs `k ≥ 5`, and the identities for `ℓ ≥ 4` range over
`4 ≤ ℓ ≤ k`. -/
theorem eq_5_4 {k : ℕ} :
    (∀ hk : 4 ≤ k,
      ∑ i ∈ Finset.Iic (⟨0, by omega⟩ : Fin k), ∑ j ∈ Finset.Iic (⟨0, by omega⟩ : Fin k),
          A53 k i j = 1 ∧
      ∑ i ∈ Finset.Iic (⟨1, by omega⟩ : Fin k), ∑ j ∈ Finset.Iic (⟨1, by omega⟩ : Fin k),
          A53 k i j = 40 / 27 ∧
      ∑ i ∈ Finset.Iic (⟨2, by omega⟩ : Fin k), ∑ j ∈ Finset.Iic (⟨2, by omega⟩ : Fin k),
          A53 k i j = 37 / 18 ∧
      ∑ i ∈ Finset.Iic (⟨3, by omega⟩ : Fin k), ∑ j ∈ Finset.Iic (⟨3, by omega⟩ : Fin k),
          A53 k i j = 7 / 3) ∧
    (∀ j : Fin k, ∀ hj : 4 ≤ j.val,
      ∑ i ∈ Finset.Iic (⟨2, by have := j.isLt; omega⟩ : Fin k), A53 k i j = 5 / 18) ∧
    (∀ ℓ : Fin k, 3 ≤ ℓ.val →
      ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic ℓ, A53 k i j =
          7 / 3 + 2 * ((ℓ.val : ℝ) + 1 - 4) * (5 / 18) ∧
      1 / ((ℓ.val : ℝ) + 1) * ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic ℓ, A53 k i j =
          1 / ((ℓ.val : ℝ) + 1) * (7 / 3 - 8 * (5 / 18)) + 2 * (5 / 18) ∧
      1 / ((ℓ.val : ℝ) + 1) * (7 / 3 - 8 * (5 / 18)) + 2 * (5 / 18) =
          1 / (9 * ((ℓ.val : ℝ) + 1)) + 5 / 9 ∧
      1 / (9 * ((ℓ.val : ℝ) + 1)) + 5 / 9 ≤ 7 / 12) := by sorry

end MultiwayCut
