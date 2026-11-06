-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_4_3
-- name    : FourierRankQLB.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:34.030176+00:00
-- url     : https://prove2.me/theorems/8ea4b597-d8a4-4aa2-909f-3671d6a048c0
-- title:
--   Lemma 4.3 — Fourier-rank growth for exact membership
-- statement:
--   Let $n\ge2$, $d=d_n$, $s>0$, and let $G\subset\mathbb R^n$ be a finite grid. After $M$ calls to exact membership for $K_{s,Q}$ on $G$, every purified algorithmic state lies in $V_M^{(d)}\mathbin{\widehat\otimes}H_{alg}$, and every final outcome probability belongs to $A_{2M}^{(d)}$.
--
--   The statement also records the fact behind this, used by the paper at p.19: the oracle family has Fourier-rank cost at most one.
--
--   Differences from the source:
--
--   - encoding: the ambient dimension $n$ of §4–5, with §5.1 fixing $n\ge2$ → hypothesis `2 ≤ n`; reason: the standing assumption; it excludes $d=0$, where $g_d$ and the radii degenerate
--   - generalization: two conclusions, on states and on outcome probabilities → also the conjunct that the oracle family has Fourier-rank cost at most one; reason: it is the first step of the printed proof; the other two conjuncts are the source's claims exactly
--   - encoding: each query slot an allowed query or inverse query, possibly controlled by the stored history, with identity padding (p.16) → every slot applies the membership oracle itself; reason: the oracle is an involution, so its inverse is itself; a controlled or identity slot is one plain query between Q-independent unitaries that swap the answer bit with a workspace qubit in the state $|+\rangle$, which the oracle fixes; the query count is unchanged
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 4.3, p.26

import Mathlib
import Definitions.Def_FourierRankQLB_hardOracle
import Definitions.Def_FourierRankQLB_HasFourierRankCost
import Definitions.Def_FourierRankQLB_Ar
import Definitions.Def_FourierRankQLB_QueryCircuit_finalState

open MeasureTheory

namespace FourierRankQLB

/-- Lemma 4.3 (Fourier-rank growth for exact membership). After `M` calls to exact membership for
`K_{s,Q}` on a finite grid, every purified algorithmic state lies in `V_M^{(d)} ⊗̂ H_alg`, and every
final outcome probability belongs to `A_{2M}^{(d)}`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 4.3, p. 26.

**Formalization Note.** The first conjunct is the cost-one fact the paper's proof establishes: the
oracle family has Fourier-rank cost at most one. A state after `M` calls is the final state of a
circuit with `C.T = M`. The grid is `Y = G` with counting measure, and `W` is any workspace. -/
theorem lemma_4_3 {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (G : Finset (Ambient n)) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] :
    HasFourierRankCost (fun Q : Od (dn n) =>
      hardOracle (Measure.count : Measure G) W Subtype.val measurable_subtype_coe s Q) 1 ∧
    ∀ C : QueryCircuit (QReg (Measure.count : Measure G) W),
      (∃ Φ ∈ VH (dn n) C.T (QReg (Measure.count : Measure G) W),
        Φ =ᵐ[haarO (dn n)] fun Q => C.finalState fun _ =>
          hardOracle (Measure.count : Measure G) W Subtype.val measurable_subtype_coe s Q) ∧
      ∀ E : QReg (Measure.count : Measure G) W →L[ℂ] QReg (Measure.count : Measure G) W,
        E.IsPositive → (1 - E).IsPositive →
        ∃ f ∈ Ar (dn n) (2 * C.T), f =ᵐ[haarO (dn n)] fun Q =>
          inner ℂ (C.finalState fun _ =>
              hardOracle (Measure.count : Measure G) W Subtype.val measurable_subtype_coe s Q)
            (E (C.finalState fun _ =>
              hardOracle (Measure.count : Measure G) W Subtype.val measurable_subtype_coe s Q)) := by sorry

end FourierRankQLB
