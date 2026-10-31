-- Prove2me | Theorems.Thm_KallMayerSLP_Recourse_lemma_2_1
-- name    : KallMayerSLP.Recourse.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:02.785107+00:00
-- url     : https://prove2.me/theorems/9a7e3082-76e2-4955-b399-62cc0aab00b0
-- title:
--   Lemma 2.1 — a rank and feasibility test for complete recourse
-- statement:
--   Let $W\in\mathbb R^{m_2\times n_2}$. The following are equivalent:
--
--   1. $W$ satisfies the complete recourse condition (2.6), $\{z\mid z=Wy,\ y\ge 0\}=\mathbb R^{m_2}$;
--   2. $\operatorname{rank}(W)=m_2$, and for **every** set $\{W_{i_1},\dots,W_{i_{m_2}}\}$ of linearly independent columns of $W$ the linear system (2.7)
--
--   $$
--   Wy=0,\qquad y_{i_k}\ge 1\ (k=1,\dots,m_2),\qquad y\ge 0
--   $$
--
--   is feasible;
--   3. $\operatorname{rank}(W)=m_2$, and for **some** set of $m_2$ linearly independent columns of $W$ the system (2.7) is feasible.
--
--   So complete recourse, a condition on infinitely many right-hand sides, reduces to a rank computation and one LP feasibility test.
--
--   **Formalization Note** A selection of columns is a map $s:\{1,\dots,m_2\}\to\{1,\dots,n_2\}$ whose columns $W_{s(k)}$ are linearly independent. The statement is the conjunction of the two equivalences 1 ⇔ 2 and 1 ⇔ 3. Complete recourse is the published `KallMayer.Recourse.CompleteRecourse`.
--
--   Differences from the source:
--   - reading: 'for an arbitrary set {W_{i1}, …, W_{im2}} of linearly independent columns of W, the constraints (2.7) are feasible' → both readings: for every such selection (1 ⇔ 2) and for some selection (1 ⇔ 3); reason: the proof of ⇒ works for any selection and the proof of ⇐ uses one; stating both covers the stronger reading of each direction
--   - encoding: a set of m₂ linearly independent columns {W_{i1}, …, W_{im2}} → `s : Fin m₂ → Fin n₂` with `LinearIndependent ℝ (fun k => Wᵀ (s k))`; reason: linear independence forces s injective; same selections
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.1, pp.201–202 (PDF 210–211)

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse

open KallMayer.Recourse (CompleteRecourse)
open Matrix

namespace KallMayerSLP.Recourse

/-- Lemma 2.1 (Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.1,
pp.201–202, PDF 210–211): a matrix `W ∈ ℝ^{m₂×n₂}` satisfies the complete recourse condition (2.6),
`{z | z = W y, y ≥ 0} = ℝ^{m₂}`, if and only if `rank(W) = m₂` and, for a set
`{W_{i₁}, …, W_{i_{m₂}}}` of linearly independent columns of `W`, the system (2.7)
`W y = 0, y_{i_k} ≥ 1 (k = 1, …, m₂), y ≥ 0` is feasible.

**Formalization Note.** "For an arbitrary set of linearly independent columns" is stated in both
readings: the first conjunct quantifies over every selection, the second asks for one selection.
A selection is `s : Fin m₂ → Fin n₂` whose columns `k ↦ Wᵀ (s k)` (the column `W_{s k}`) are linearly
independent (which forces `s` injective). The complete recourse condition is the published
`KallMayer.Recourse.CompleteRecourse`. -/
theorem lemma_2_1 {m₂ n₂ : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ) :
    (CompleteRecourse W ↔
      W.rank = m₂ ∧
        ∀ s : Fin m₂ → Fin n₂, LinearIndependent ℝ (fun k => W.transpose (s k)) →
          ∃ y : Fin n₂ → ℝ, W *ᵥ y = 0 ∧ (∀ k, 1 ≤ y (s k)) ∧ 0 ≤ y) ∧
    (CompleteRecourse W ↔
      W.rank = m₂ ∧
        ∃ s : Fin m₂ → Fin n₂, LinearIndependent ℝ (fun k => W.transpose (s k)) ∧
          ∃ y : Fin n₂ → ℝ, W *ᵥ y = 0 ∧ (∀ k, 1 ≤ y (s k)) ∧ 0 ≤ y) := by sorry

end KallMayerSLP.Recourse
