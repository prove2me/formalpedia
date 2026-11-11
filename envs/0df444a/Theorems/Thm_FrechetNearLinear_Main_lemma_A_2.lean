-- Prove2me | Theorems.Thm_FrechetNearLinear_Main_lemma_A_2
-- name    : FrechetNearLinear.Main.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:36:52.691604+00:00
-- url     : https://prove2.me/theorems/7183710f-5fd7-4130-ab2c-cc46493f59b3
-- title:
--   Lemma A.2 — seed: a linear-time matching of cost U with D* ≤ U ≤ (2(m+n)+1)D* (continuous), (4(m+n)+1)D* (discrete)
-- statement:
--   Fix $d$. There are admissible programs and a constant $C$ (depending on $d$) such that, for all $1\le m\le n$ and all $P\in(\mathbb R^d)^n$, $Q\in(\mathbb R^d)^m$, within $C(m+n)$ steps:
--
--   - the first program outputs a matching of $P$ and $Q$ — the vertex list $w$ of a bi-monotone polygonal path in the free-space diagram from $(0,0)$ to $(n-1,m-1)$ — and its cost $U=\max_{(x,y)\in w}\|P(x)-Q(y)\|$, with
--   $$d_F(P,Q)\le U\le\big(2(m+n)+1\big)\,d_F(P,Q);$$
--   - the second outputs a discrete matching $c$ and its cost $U$, with
--   $$\tilde d_F(P,Q)\le U\le\big(4(m+n)+1\big)\,\tilde d_F(P,Q).$$
--
--   In both cases $U=0$ if and only if the distance is $0$. Output: $U$ in $M[-1]$, the number of vertices (pairs) in $M[-2]$, and the $k$-th vertex in $(M[-3-2k],M[-4-2k])$.
--
--   The seed brackets the distance within a factor $O(m+n)$, which is what lets the threshold search of Lemma A.1 use only $O(\log\log(m+n+2))$ decision calls.
--
--   Differences from the source:
--   - reading: "In O(m + n) time, one can compute a matching … of cost U" → an admissible program on the mission's real RAM accepting within $C(m+n)$ steps on every input, with $C$ depending only on $d$, and $U$ and the matching in the stated output layout; reason: the paper names no machine; $d$ is fixed
--   - encoding: a matching of $P$ and $Q$ → a bi-monotone polygonal path in the free-space diagram from $(0,0)$ to $(n-1,m-1)$ given by its vertex list, its cost the maximum of $\|P(x)-Q(y)\|$ over its points; reason: the paper identifies a matching with its path in the diagram (p. 3)
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 35, Lemma A.2

import Mathlib
import Definitions.Def_FrechetNearLinear_Main_Frechet
import Definitions.Def_FrechetNearLinear_Main_FreeSpace
import Definitions.Def_FrechetNearLinear_Main_Machine

namespace FrechetNearLinear.Main

/-- Lemma A.2 (Seed), p. 35. For every dimension `d` there are admissible programs and a constant
`C` such that on every input `P ∈ (ℝ^d)^n`, `Q ∈ (ℝ^d)^m` with `1 ≤ m ≤ n`, within
`C · (m + n)` steps: (continuous) the first program outputs a matching of `P` and `Q`, as the
vertex list `w` of a bi-monotone polygonal path from `(0, 0)` to `(n - 1, m - 1)` in the
free-space diagram, together with its cost `U`, and `d_F ≤ U ≤ (2(m+n)+1) d_F`; (discrete) the
second outputs a discrete matching `c` with its cost `U`, and `d̃_F ≤ U ≤ (4(m+n)+1) d̃_F`. In
both cases `U = 0` if and only if the distance is `0`. -/
theorem lemma_A_2 (d : ℕ) :
    (∃ A : Program, Admissible A ∧ ∃ C : ℝ,
      ∀ n m : ℕ, 1 ≤ m → m ≤ n → ∀ (P : Fin n → E d) (Q : Fin m → E d),
        ∃ (U : ℝ) (w : List (ℝ × ℝ)),
          ComputesValueListWithin A (curveInput P Q) (C * ((m : ℝ) + n)) U w ∧
          IsMonoPolyline w (0, 0) ((n : ℝ) - 1, (m : ℝ) - 1) ∧
          U = sSup ((fun z : ℝ × ℝ => ‖curvePt P z.1 - curvePt Q z.2‖) '' polyline w) ∧
          frechetDist P Q ≤ U ∧ U ≤ (2 * ((m : ℝ) + n) + 1) * frechetDist P Q ∧
          (U = 0 ↔ frechetDist P Q = 0)) ∧
    (∃ A : Program, Admissible A ∧ ∃ C : ℝ,
      ∀ n m : ℕ, 1 ≤ m → m ≤ n → ∀ (P : Fin n → E d) (Q : Fin m → E d),
        ∃ (U : ℝ) (c : List (ℕ × ℕ)),
          ComputesValueListWithin A (curveInput P Q) (C * ((m : ℝ) + n)) U
            (c.map fun ij => ((ij.1 : ℝ), (ij.2 : ℝ))) ∧
          IsCoupling n m c ∧ U = couplingCost P Q c ∧
          discreteFrechetDist P Q ≤ U ∧ U ≤ (4 * ((m : ℝ) + n) + 1) * discreteFrechetDist P Q ∧
          (U = 0 ↔ discreteFrechetDist P Q = 0)) := by sorry

end FrechetNearLinear.Main
