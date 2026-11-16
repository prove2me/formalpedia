-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_7_2
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:07:51.79852+00:00
-- url     : https://prove2.me/theorems/ca7c9a58-4520-4eed-b165-f99af168be96
-- title:
--   Theorem 7.2 — an integer alphabet for the radius
-- statement:
--   Let $\epsilon=0$, let the weights be nonnegative and normalized, and consider the weighted radius $R^*_{Q,w}$ (Remark 6.5) for a fixed set $Q$ of exact audits.
--
--   1. If $Q=\emptyset$ and $2b\ge n$ the radius is infinite.
--   2. Otherwise put $M_Q=\min\{2b,n-|Q|\}$ and $\kappa_Q=\min\{M_Q,n-M_Q\}$. The radius, an extremal hidden region $S$ ($S\subseteq V\setminus Q$, $|S|\le M_Q$, $\sum_vw_vg_{S,Q}(v)=R^*_{Q,w}$) and its envelope $g_{S,Q}$ can be computed; on a tree this takes $O(n(M_Q+1)(\kappa_Q+1))=O(n(b+1)^2)$ operations and space.
--   3. On a graph given with a nice tree decomposition of width $\omega$ as in Theorem 5.2 it takes $O((M_Q+1)^{\omega+1}n(\omega+\kappa_Q+1)^2)$ operations, which is fixed-parameter tractable in $b+\omega$.
--   4. Without audits, every $\epsilon\ge0$ is handled by adding $\epsilon$ to the noiseless radius.
--
--   **Formalization Note** The output gives the radius, the indicator of $S$ and the values of $g_{S,Q}$. The fixed-parameter bound is $f(b+\omega)(n+1)^c$ with $f$ computable.
--
--   Differences from the source:
--   - encoding: O(·) arithmetic operations (and space) → one fixed program of the unit-cost real RAM and one constant C>0 chosen before every instance, every executed instruction charged, space = distinct cells accessed; reason: the paper's model counts exact arithmetic operations and comparisons; charging all instructions only strengthens the bound
--   - reading: can be computed without forming pairwise distances → only the operation and space bounds are stated; reason: the phrase describes the method; the bounds are the formal content
--   - reading: Without audits, every ε ≥ 0 is handled by adding ε to the noiseless radius → R*_{∅,w}(ε) = ε + R*_{∅,w}(0) for every b ≤ n (both sides infinite when 2b ≥ n); reason: the radius identity behind the algorithmic remark
--   - reading: O(n(M_Q+1)(κ_Q+1)) = O(n(b+1)²) → both bounds hold for the same run and constant; reason: the second bound follows from M_Q ≤ 2b
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 7.2, printed pp.21–22 (PDF pp.23–24); weighted radius per Remark 6.5, printed p.21 (PDF p.23)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_RAM

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 7.2, printed pp.21–22 / PDF pp.23–24. `ε = 0`, nonnegative normalized weights, the
weighted radius `R*_{Q,w}` of Remark 6.5 for exact audits `Q`.
1. If `Q = ∅` and `2b ≥ n` the radius is infinite.
2. Otherwise, with `M_Q = min{2b, n − |Q|}`, `κ_Q = min{M_Q, n − M_Q}`, one fixed program
   computes on trees the radius, an extremal hidden region `S` (`S ⊆ V ∖ Q`, `|S| ≤ M_Q`,
   `∑_v w_v g_{S,Q}(v) = R*_{Q,w}`) and its envelope `g_{S,Q}`, within `C n (M_Q + 1)(κ_Q + 1)`
   and `C n (b + 1)²` operations and cells.
3. For all `C₁, C₂`, one fixed program does the same given a nice tree decomposition of width
   `ω` (at most `C₁ n` join and `C₂ (ω + 1) n` other nodes) within
   `C (M_Q + 1)^{ω+1} n (ω + κ_Q + 1)²` operations, and within `f(b + ω) (n + 1)^c` (`f` computable).
4. Without audits, every `ε ≥ 0` adds `ε`: `R*_{∅,w}(ε) = ε + R*_{∅,w}(0)` (both sides `∞` if `2b ≥ n`).
Output: `R[0]` the radius, `I[1+v] = 1` iff `v ∈ S`, `R[1+v] = g_{S,Q}(v)`. -/
theorem theorem_7_2 :
    (∀ {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L : ℝ) (w : Fin n → ℝ),
      1 ≤ n → G.Connected → 0 < L → (∀ v, 0 ≤ w v) → ∑ v, w v = 1 → b ≤ n → n ≤ 2 * b →
      minimaxRadius G b L 0 ∅ w = ⊤) ∧
    (∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L : ℝ) (Q : Finset (Fin n)) (w : Fin n → ℝ),
        1 ≤ n → G.IsTree → 0 < L → (∀ v, 0 ≤ w v) → ∑ v, w v = 1 → b ≤ n →
        (Q.Nonempty ∨ 2 * b < n) →
        ∃ fin, RunsWithin P (fun _ _ => 0)
            (encInst (exactInst G b L 0 Q w 0 0)).1 (encInst (exactInst G b L 0 Q w 0 0)).2
            (min (C * n * (min (2 * b) (n - Q.card) + 1) *
                (min (min (2 * b) (n - Q.card)) (n - min (2 * b) (n - Q.card)) + 1))
              (C * n * (b + 1) ^ 2))
            (min (C * n * (min (2 * b) (n - Q.card) + 1) *
                (min (min (2 * b) (n - Q.card)) (n - min (2 * b) (n - Q.card)) + 1))
              (C * n * (b + 1) ^ 2)) fin ∧
          0 ≤ fin.rmem 0 ∧ ENNReal.ofReal (fin.rmem 0) = minimaxRadius G b L 0 Q w ∧
          Disjoint (Finset.univ.filter fun v : Fin n => fin.imem (1 + v.val) = 1) Q ∧
          (Finset.univ.filter fun v : Fin n => fin.imem (1 + v.val) = 1).card ≤
            min (2 * b) (n - Q.card) ∧
          ∑ v, ENNReal.ofReal (w v) *
              gSQ G L 0 (Finset.univ.filter fun v : Fin n => fin.imem (1 + v.val) = 1) Q v =
            minimaxRadius G b L 0 Q w ∧
          ∀ v, 0 ≤ fin.rmem (1 + v.val) ∧ ENNReal.ofReal (fin.rmem (1 + v.val)) =
            gSQ G L 0 (Finset.univ.filter fun v : Fin n => fin.imem (1 + v.val) = 1) Q v) ∧
    (∀ C₁ C₂ : ℕ, ∃ (P : Program) (C : ℕ) (f : ℕ → ℕ) (c : ℕ), 0 < C ∧ Computable f ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L : ℝ) (Q : Finset (Fin n)) (w : Fin n → ℝ)
        (T : NiceTD n) (ω : ℕ),
        1 ≤ n → G.Connected → 0 < L → (∀ v, 0 ≤ w v) → ∑ v, w v = 1 → b ≤ n →
        (Q.Nonempty ∨ 2 * b < n) → IsNiceTD G T ω →
        T.joinCount ≤ C₁ * n → T.otherCount ≤ C₂ * (ω + 1) * n →
        ∃ fin, RunsWithin P (fun _ _ => 0)
            ((encInst (exactInst G b L 0 Q w 0 0)).1 ++ encTD T)
            (encInst (exactInst G b L 0 Q w 0 0)).2
            (min (C * (min (2 * b) (n - Q.card) + 1) ^ (ω + 1) * n *
                (ω + min (min (2 * b) (n - Q.card)) (n - min (2 * b) (n - Q.card)) + 1) ^ 2)
              (f (b + ω) * (n + 1) ^ c))
            (3 * min (C * (min (2 * b) (n - Q.card) + 1) ^ (ω + 1) * n *
                (ω + min (min (2 * b) (n - Q.card)) (n - min (2 * b) (n - Q.card)) + 1) ^ 2)
              (f (b + ω) * (n + 1) ^ c)) fin ∧
          0 ≤ fin.rmem 0 ∧ ENNReal.ofReal (fin.rmem 0) = minimaxRadius G b L 0 Q w ∧
          Disjoint (Finset.univ.filter fun v : Fin n => fin.imem (1 + v.val) = 1) Q ∧
          (Finset.univ.filter fun v : Fin n => fin.imem (1 + v.val) = 1).card ≤
            min (2 * b) (n - Q.card) ∧
          ∑ v, ENNReal.ofReal (w v) *
              gSQ G L 0 (Finset.univ.filter fun v : Fin n => fin.imem (1 + v.val) = 1) Q v =
            minimaxRadius G b L 0 Q w ∧
          ∀ v, 0 ≤ fin.rmem (1 + v.val) ∧ ENNReal.ofReal (fin.rmem (1 + v.val)) =
            gSQ G L 0 (Finset.univ.filter fun v : Fin n => fin.imem (1 + v.val) = 1) Q v) ∧
    (∀ {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L ε : ℝ) (w : Fin n → ℝ),
      1 ≤ n → G.Connected → 0 < L → 0 ≤ ε → (∀ v, 0 ≤ w v) → ∑ v, w v = 1 → b ≤ n →
      minimaxRadius G b L ε ∅ w = ENNReal.ofReal ε + minimaxRadius G b L 0 ∅ w) := by sorry

end MeanCertificates1424.Hardness.Supplement
