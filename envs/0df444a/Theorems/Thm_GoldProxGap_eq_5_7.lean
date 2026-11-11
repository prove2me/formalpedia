-- Prove2me | Theorems.Thm_GoldProxGap_eq_5_7
-- name    : GoldProxGap.eq_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:05.019199+00:00
-- url     : https://prove2.me/theorems/4ca8c4e6-6bdf-46db-9dc8-dfe01e6a0e68
-- title:
--   Equation (5.7) — the Delsarte–Goethals moment identity $\sum_{j\le s}[n-j\ n-s]_4\,\pi_j(r)=2^{(d-\iota)s}[n-r\ s]_4$
-- statement:
--   **Equation (5.7) (Delsarte–Goethals moment identity).** Let $n=\lfloor d/2\rfloor$ and $\iota=1$ for even $d$, $\iota=0$ for odd $d$. For alternating binary $d\times d$ matrices put $\langle A,B\rangle=\sum_{i<j}A_{ij}B_{ij}\in\mathbb F_2$ and, for an alternating $A$,
--   $$
--   \pi_j(A)=\sum_{B\ \text{alternating},\ \operatorname{rank}B=2j}(-1)^{\langle A,B\rangle}.
--   $$
--   Then $\pi_j(A)$ depends only on the rank $2r$ of $A$, and for $0\le s,r\le n$
--   $$
--   \sum_{j=0}^{s}\begin{bmatrix}n-j\\ n-s\end{bmatrix}_4\pi_j(r)=2^{(d-\iota)s}\begin{bmatrix}n-r\\ s\end{bmatrix}_4 .
--   $$
--
--   The paper takes this identity from Delsarte and Goethals (1975, Eq. (29)); it is the character-sum input of the matrix count in Lemma 5.13.
--
--   **Formalization Note** The sums are real numbers; $[a\ b]_4$ is `gaussBinom 4 a b`. The identity is stated for every alternating $A$ of rank $2r$ and every $s\le n$.
--
--   Differences from the source:
--   - encoding: π_j(r) = Σ_{rank B=2j} χ_B(A) depends only on r → π_j(A) written out as a sum over alternating B of rank 2j, with a clause that matrices of equal rank have equal sums; reason: same claim
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), proof of Lemma 5.13, eq. (5.7), p.43

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_GoldProxGap_goldMoment

open scoped Classical

namespace GoldProxGap

/-- **Equation (5.7), the moment identity of Delsarte and Goethals**, p.43 (proof of Lemma 5.13).
Dao, Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary
Fields*, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…).

"For 0 ≤ j ≤ n and a matrix A of rank 2r, the sum π_j(r) = Σ_{rank B=2j} χ_B(A) depends only on r
[…]. The moment identity of Delsarte and Goethals [22, Eq. (29)], also stated in [44, Eq. (13)],
gives for 0 ≤ s, r ≤ n
Σ_{j=0}^{s} [n−j  n−s]₄ π_j(r) = 2^{(d−ι)s} [n−r  s]₄. (5.7)"

Here (p.42) `⟨A, B⟩ = Σ_{i<j} A_ij B_ij ∈ F₂` and `χ_B(A) = (−1)^{⟨A,B⟩}`, the sums run over
alternating binary `d × d` matrices, `n = ⌊d/2⌋`, and `ι = 1` for even `d`, `0` for odd `d`.

**Formalization Note.** `π_j(A)` is the sum over alternating `B` of rank `2j` of
`(−1)^{⟨A,B⟩}` (as a real number). The first clause is "depends only on r": two alternating
matrices of the same rank have the same sums. The identity is stated for every alternating `A`
of rank `2r` and every `s ≤ n` (then `r ≤ n` automatically). `[a b]₄` is
`HScattered.Hyperplanes.gaussBinom 4 a b`. -/
theorem eq_5_7 (d : ℕ) :
    let n := d / 2
    let ι := if Even d then 1 else 0
    let π : ℕ → Matrix (Fin d) (Fin d) (ZMod 2) → ℝ := fun j A =>
      ∑ Bm ∈ Finset.univ.filter (fun Bm : Matrix (Fin d) (Fin d) (ZMod 2) =>
        IsAltBin Bm ∧ Bm.rank = 2 * j), (-1 : ℝ) ^ (altPairing A Bm).val
    (∀ (j : ℕ) (A A' : Matrix (Fin d) (Fin d) (ZMod 2)), IsAltBin A → IsAltBin A' →
      A.rank = A'.rank → π j A = π j A') ∧
    ∀ (A : Matrix (Fin d) (Fin d) (ZMod 2)) (r s : ℕ), IsAltBin A → A.rank = 2 * r → s ≤ n →
      ∑ j ∈ Finset.range (s + 1),
          HScattered.Hyperplanes.gaussBinom 4 (n - j) (n - s) * π j A =
        (2 : ℝ) ^ ((d - ι) * s) * HScattered.Hyperplanes.gaussBinom 4 (n - r) s := by sorry

end GoldProxGap
