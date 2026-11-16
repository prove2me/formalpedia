-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_A_2
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:08:24.714563+00:00
-- url     : https://prove2.me/theorems/41efe0a5-e253-43bd-bf24-dbfd042119e1
-- title:
--   Theorem A.2 — exact cycle risk and optimal audit placement
-- statement:
--   Let $G=C_n$, $n\ge3$, $\epsilon=0$, $1\le k\le n$. A $k$-set of audits cuts the cycle into gaps of unaudited vertices with lengths $g_1\ge\dots\ge g_k\ge0$ and total $n-k$. Let $F(a)=\lfloor(a+1)^2/4\rfloor$, $m\ge0$ an integer and $M=\min\{m,n-k\}$. For every fixed audit set,
--   $$\Psi_{C_n,Q}(m)=\max\Big\{\sum_{j=1}^kF(t_j):0\le t_j\le g_j,\ t_j\in\mathbb Z,\ \sum_jt_j=M\Big\}=\sum_{j=1}^kF(t^*_j),\qquad t^*_j=\min\Big\{g_j,\Big(M-\sum_{i<j}g_i\Big)_+\Big\}.$$
--   Among all $k$-sets, a placement whose gap lengths differ by at most one minimizes $\Psi_{C_n,Q}(m)$ for every $m$, and hence the risk; with $a=\lfloor(n-k)/k\rfloor$ and $r=n-k-ak$, its value is obtained by substituting $r$ gaps of length $a+1$ and $k-r$ gaps of length $a$ into (A.2). A given placement is evaluated in $O(n+k\log k)$ time, and an optimal placement and its risk are found in $O(n)$ time.
--
--   **Formalization Note** In the second formula natural-number subtraction is the positive part. The evaluation program receives the audit positions in arbitrary order and outputs $\Psi_{C_n,Q}(m)$; the placement program receives $n,k,b,L$ and outputs $k$ positions and the risk $R^*_Q(C_n,b,L,0)$.
--
--   Differences from the source:
--   - encoding: O(·) arithmetic operations (and space) → one fixed program of the unit-cost real RAM and one constant C>0 chosen before every instance, every executed instruction charged, space = distinct cells accessed; reason: the paper's model counts exact arithmetic operations and comparisons; charging all instructions only strengthens the bound
--   - reading: a placement whose gap lengths differ by at most one minimizes → balanced placements exist, and every balanced placement minimizes; reason: the source's proof shows every such gap vector is realizable and optimal
--   - encoding: the risk → R*_Q(C_n,b,L,0) for every b ≤ n and L > 0; reason: the risk is the case m = 2b by Theorem 6.4
--   - encoding: a given placement is evaluated → the program outputs Ψ_{C_n,Q}(m); reason: the risk is L Ψ_{C_n,Q}(2b)/n
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem A.2, printed p.23 (PDF p.25), proof to printed p.24 (PDF p.26)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_RAM

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem A.2, printed p.23 / PDF p.25 (proof to p.24 / PDF p.26). On `C_n` (`n ≥ 3`, unit
lengths, `ε = 0`) with a `k`-set of audits `Q` (`1 ≤ k ≤ n`), sorted gaps `g₁ ≥ ⋯ ≥ g_k ≥ 0`
(`∑ g_j = n − k`), any integer `m ≥ 0` and `M = min{m, n − k}`:
1. `Ψ_{C_n,Q}(m) = max{∑_j F(t_j) : 0 ≤ t_j ≤ g_j, t_j ∈ ℤ, ∑ t_j = M} = ∑_j F(t*_j)` with
   `t*_j = min{g_j, (M − ∑_{i<j} g_i)_+}` (natural subtraction is the positive part);
2. balanced placements (gap lengths differing by at most one) exist and minimize
   `Ψ_{C_n,Q}(m)` for every `m` and the risk `R*_Q(C_n, b, L, 0)` for every `b, L`, with value
   (A.2) at `r` gaps `a + 1` and `k − r` gaps `a`, `a = ⌊(n − k)/k⌋`, `r = n − k − a k`;
3. one fixed program evaluates `Ψ_{C_n,Q}(m)` of a given placement (listed in any order) in
   `C (n + k log k)` time, and one fixed program finds an optimal placement and its risk in
   `C n` time. -/
theorem theorem_A_2 :
    (∀ (n k : ℕ) (Q : Finset (Fin n)) (m : ℕ), 3 ≤ n → 1 ≤ k → Q.card = k →
      IsGreatest {s : ℕ | ∃ t : ℕ → ℕ, (∀ j, j < k → t j ≤ gapAt n Q j) ∧
          ∑ j ∈ Finset.range k, t j = min m (n - k) ∧ s = ∑ j ∈ Finset.range k, Fcyc (t j)}
        (∑ j ∈ Finset.range k, Fcyc (min (gapAt n Q j)
          (min m (n - k) - ∑ i ∈ Finset.range j, gapAt n Q i))) ∧
      PsiQ (SimpleGraph.cycleGraph n) Q m = ((∑ j ∈ Finset.range k, Fcyc (min (gapAt n Q j)
          (min m (n - k) - ∑ i ∈ Finset.range j, gapAt n Q i)) : ℕ) : ℕ∞)) ∧
    (∀ n k : ℕ, 3 ≤ n → 1 ≤ k → k ≤ n → ∃ Q₀ : Finset (Fin n), Q₀.card = k ∧ Balanced n Q₀) ∧
    (∀ (n k : ℕ) (Q₀ : Finset (Fin n)), 3 ≤ n → 1 ≤ k → Q₀.card = k → Balanced n Q₀ →
      (∀ Q : Finset (Fin n), Q.card = k → ∀ m : ℕ,
        PsiQ (SimpleGraph.cycleGraph n) Q₀ m ≤ PsiQ (SimpleGraph.cycleGraph n) Q m) ∧
      (∀ Q : Finset (Fin n), Q.card = k → ∀ (b : ℕ) (L : ℝ), 0 < L → b ≤ n →
        minimaxRadius (SimpleGraph.cycleGraph n) b L 0 Q₀ (uniformW n) ≤
          minimaxRadius (SimpleGraph.cycleGraph n) b L 0 Q (uniformW n)) ∧
      ∀ m : ℕ, PsiQ (SimpleGraph.cycleGraph n) Q₀ m =
        ((∑ j ∈ Finset.range k,
          Fcyc (min (if j < n - k - (n - k) / k * k then (n - k) / k + 1 else (n - k) / k)
            (min m (n - k) - ∑ i ∈ Finset.range j,
              (if i < n - k - (n - k) / k * k then (n - k) / k + 1 else (n - k) / k))) : ℕ) :
          ℕ∞)) ∧
    (∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ (n k m : ℕ) (l : List (Fin n)), 3 ≤ n → 1 ≤ k → l.Nodup → l.length = k →
        ∃ fin, RunsWithin P (fun _ _ => 0) ([n, k, m] ++ l.map Fin.val) []
            ⌊(C : ℝ) * (n + k * Real.log k)⌋₊ (3 * ⌊(C : ℝ) * (n + k * Real.log k)⌋₊) fin ∧
          ((fin.imem 0 : ℕ) : ℕ∞) = PsiQ (SimpleGraph.cycleGraph n) l.toFinset m) ∧
    (∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ (n k b : ℕ) (L : ℝ), 3 ≤ n → 1 ≤ k → k ≤ n → b ≤ n → 0 < L →
        ∃ fin, RunsWithin P (fun _ _ => 0) [n, k, b] [L] (C * n) (3 * (C * n)) fin ∧
          ((List.range k).map fun j => fin.imem (1 + j)).Nodup ∧
          (∀ j, j < k → fin.imem (1 + j) < n) ∧
          ∀ Q₀ : Finset (Fin n), (Q₀.image Fin.val : Finset ℕ) =
              ((List.range k).map fun j => fin.imem (1 + j)).toFinset →
            (∀ Q : Finset (Fin n), Q.card = k →
              minimaxRadius (SimpleGraph.cycleGraph n) b L 0 Q₀ (uniformW n) ≤
                minimaxRadius (SimpleGraph.cycleGraph n) b L 0 Q (uniformW n)) ∧
            0 ≤ fin.rmem 0 ∧ ENNReal.ofReal (fin.rmem 0) =
              minimaxRadius (SimpleGraph.cycleGraph n) b L 0 Q₀ (uniformW n)) := by sorry

end MeanCertificates1424.Hardness.Supplement
