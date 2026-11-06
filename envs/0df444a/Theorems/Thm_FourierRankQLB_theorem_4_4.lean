-- Prove2me | Theorems.Thm_FourierRankQLB_theorem_4_4
-- name    : FourierRankQLB.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:22.287051+00:00
-- url     : https://prove2.me/theorems/1a1d17fd-d1fa-4437-91b4-e2e67c72346d
-- title:
--   Theorem 4.4 — determinant lower bound for exact membership
-- statement:
--   Let $n\ge2$, $d=d_n$ and $s>0$. Any algorithm which predicts $\det Q$ for $Q\sim\mu_d$ with average success probability greater than $1/2$, using only exact membership for $K_{s,Q}$ on a finite grid fixed in advance, makes at least $d/2$ queries.
--
--   Fewer queries give average success exactly $1/2$, so any positive advantage already forces the bound.
--
--   Differences from the source:
--
--   - encoding: the ambient dimension $n$ of §4–5, with §5.1 fixing $n\ge2$ → hypothesis `2 ≤ n`; reason: the standing assumption; it excludes $d=0$, where $g_d$ and the radii degenerate
--   - encoding: the algorithm predicts $\det Q$ → a POVM on `Bool`, with `true` coding $+1$; reason: a two-outcome measurement is exactly such a POVM
--   - encoding: each query slot an allowed query or inverse query, possibly controlled by the stored history, with identity padding (p.16) → every slot applies the membership oracle itself; reason: the oracle is an involution, so its inverse is itself; a controlled or identity slot is one plain query between Q-independent unitaries that swap the answer bit with a workspace qubit in the state $|+\rangle$, which the oracle fixes; the query count is unchanged
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 4.4, p.27

import Mathlib
import Definitions.Def_FourierRankQLB_hardOracle
import Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb
import Definitions.Def_FourierRankQLB_boolSign
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory

namespace FourierRankQLB

/-- Theorem 4.4 (Determinant lower bound for exact membership). Any algorithm which predicts `det Q`
for `Q ∼ μ_d` with average success probability greater than `1/2`, using only exact membership for
`K_{s,Q}` on a finite grid fixed in advance, makes at least `d/2` queries.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 4.4, p. 27.

**Formalization Note.** The algorithm has a two-outcome POVM on `Bool`, with `true` coding the
prediction `+1`. The grid `G` and the algorithm are fixed before `Q`, and `W` is any workspace. -/
theorem theorem_4_4 {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (G : Finset (Ambient n)) {W : Type}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (A : QueryAlg (QReg (Measure.count : Measure G) W) Bool)
    (hsucc : 1 / 2 < ∫ Q : Od (dn n), A.outcomeProb (fun _ =>
        hardOracle (Measure.count : Measure G) W Subtype.val measurable_subtype_coe s Q)
      {b | boolSign b = (Q : Matrix (Fin (dn n)) (Fin (dn n)) ℝ).det} ∂haarO (dn n)) :
    (dn n : ℝ) / 2 ≤ A.T := by sorry

end FourierRankQLB
