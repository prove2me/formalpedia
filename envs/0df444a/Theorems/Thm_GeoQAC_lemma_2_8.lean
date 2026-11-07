-- Prove2me | Theorems.Thm_GeoQAC_lemma_2_8
-- name    : GeoQAC.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:08.954199+00:00
-- url     : https://prove2.me/theorems/52acb074-4d95-4023-87ff-0e6119b01eaf
-- title:
--   Lemma 2.8 — exact amplification of approximate nekomata in depth $O(d/(\sqrt{2p}-1))$
-- statement:
--   Let $C$ be a depth-$d$ QAC circuit, $d\ge1$, synthesizing a $p$-approximate $n$-nekomata, where $p>1/2$. Then an exact $(n+2)$-nekomata can be synthesized in depth
--   $$
--   O\Big(\frac{d}{\sqrt{2p}-1}\Big).
--   $$
--   Moreover, if $C$ is a $[w,h]$-2D-QAC circuit whose targets fill a boundary column, exact synthesis is possible with a $[w+O(1),h+O(1)]$-2D-QAC circuit with the same depth bound. For a fixed constant $p>1/2$, this conversion preserves polynomial size and constant depth, and hence also 2D-QAC$^0$.
--
--   In the unrestricted case the exact circuit uses at most $|V|+O(1)$ qubits, $V$ being the qubits of $C$; in the geometric case its $n+2$ targets occupy consecutive rows of one boundary column. One absolute constant serves every $O(\cdot)$.
--
--   Differences from the source:
--   - generalization: no target placement in the geometric clause → the $n+2$ new targets occupy consecutive rows of a boundary column; reason: the proof (p.41) adds "the two targets and the flag in a constant number of rows extending the target column", and Theorem 4.1(d) needs consecutive boundary targets for Proposition 2.7.
--   - generalization: "preserves polynomial size" in the unrestricted case → the exact circuit has at most $|V|+K$ qubits; reason: the proof (p.41) says "It needs $n+a+O(1)$ qubits"; with the depth bound this gives polynomial size.
--   - encoding: "targets fill a boundary column" → the grid has $w=n$ rows and target $i$ is at $(i,c)$ for a boundary column $c$; reason: a column has $w$ positions, so filling it with the $n$ targets means $n=w$.
--   - encoding: "preserves polynomial size and constant depth" in the geometric case → the bounds $w'\le n+K$, $h'\le h+K$ and the depth bound; reason: these imply polynomial size and, for fixed $p$, constant depth.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Lemma 2.8, p.12 (restated p.40, proved p.41)

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_IsNekomataApprox

namespace GeoQAC

/-- **Lemma 2.8** (arXiv:2604.07178, version of 2026-11-03, p.12; proved p.41). Let `C` be a depth-`d`
QAC circuit synthesizing a `p`-approximate `n`-nekomata, where `p > 1/2`. Then, an exact
`(n+2)`-nekomata can be synthesized in depth `O(d/(√(2p) − 1))`. Moreover, if `C` is a
`[w, h]`-2D-QAC circuit whose targets fill a boundary column, exact synthesis is possible with a
`[w + O(1), h + O(1)]`-2D-QAC circuit with the same depth bound. For a fixed constant `p > 1/2`, this
conversion preserves polynomial size and constant depth, and hence also 2D-QAC⁰.

**Formalization Note.**
* Synthesis depth `d ≥ 1` (p.12: "for synthesis depth d ≥ 1"). One absolute constant `K` serves
  every `O(·)`.
* First clause: unrestricted geometry (any finite qubit type `V`; supports need not be intervals);
  the exact circuit has qubits `Fin N` with `N ≤ |V| + K` (the proof, p.41: "It needs n + a + O(1)
  qubits"). Together with the depth bound this gives the polynomial-size sentence.
* Second clause: "targets fill a boundary column" with `w = n` rows: target `i` is at `(i, c)` for
  a boundary column `c`. The new grid has `w' ≤ n + K` rows and `h' ≤ h + K` columns, so its size is
  polynomial. Placement clause from the proof (p.41: "add the two targets and the flag in a constant
  number of rows extending the target column"): the `n + 2` new targets occupy consecutive rows of
  one boundary column. This is a stronger conclusion than the printed lemma.
* `√(2p)` is `Real.sqrt (2 * p)`; the division is real. -/
theorem lemma_2_8 : ∃ K : ℝ, 0 < K ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (n d : ℕ) (C : QACCircuit V d) (tgt : Fin n ↪ V)
      (p : ℝ), 1 ≤ d → 1 / 2 < p → IsNekomataApprox p C tgt →
      ∃ (N D : ℕ) (C' : QACCircuit (Fin N) D) (tgt' : Fin (n + 2) ↪ Fin N),
        IsNekomataApprox 1 C' tgt' ∧ (D : ℝ) ≤ K * d / (Real.sqrt (2 * p) - 1) ∧
        (N : ℝ) ≤ Fintype.card V + K) ∧
    (∀ (n h d : ℕ) (C : QACCircuit (Pos n h) d) (tgt : Fin n ↪ Pos n h) (c : Fin h) (p : ℝ),
      1 ≤ d → 1 / 2 < p → C.Is2D → IsBoundaryCol c → (∀ i, tgt i = (i, c)) →
      IsNekomataApprox p C tgt →
      ∃ (w' h' D : ℕ) (C' : QACCircuit (Pos w' h') D) (tgt' : Fin (n + 2) ↪ Pos w' h')
        (c' : Fin h') (r₀ : ℕ),
        C'.Is2D ∧ (w' : ℝ) ≤ n + K ∧ (h' : ℝ) ≤ h + K ∧
        (D : ℝ) ≤ K * d / (Real.sqrt (2 * p) - 1) ∧
        IsBoundaryCol c' ∧ (∀ i, (tgt' i).2 = c' ∧ (tgt' i).1.val = r₀ + i.val) ∧
        IsNekomataApprox 1 C' tgt') := by sorry

end GeoQAC
