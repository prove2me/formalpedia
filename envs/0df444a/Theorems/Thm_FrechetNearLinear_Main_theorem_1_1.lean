-- Prove2me | Theorems.Thm_FrechetNearLinear_Main_theorem_1_1
-- name    : FrechetNearLinear.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:36:50.812088+00:00
-- url     : https://prove2.me/theorems/8adcbb8d-4976-475e-80f1-9b297702a4c2
-- title:
--   Theorem 1.1 — a deterministic f(1/ε)-approximation of the continuous and discrete Fréchet distance in O(n^{1+ε}) time
-- statement:
--   For every dimension $d\ge1$ there is a function $f:(0,\infty)\to[1,\infty)$ such that for every $\varepsilon>0$ there are deterministic programs $A$ and $\tilde A$ and a constant $C$ (depending only on $d$ and $\varepsilon$) with the following property. For all $1\le m\le n$ and all polygonal curves $P\in(\mathbb R^d)^n$, $Q\in(\mathbb R^d)^m$, started on the input $(P,Q)$, $A$ halts within $C\,n^{1+\varepsilon}$ steps with an output $\hat D$ satisfying
--   $$d_F(P,Q)\le\hat D\le f(1/\varepsilon)\,d_F(P,Q),$$
--   and $\tilde A$ halts within $C\,n^{1+\varepsilon}$ steps with an output $\hat D$ satisfying $\tilde d_F(P,Q)\le\hat D\le f(1/\varepsilon)\,\tilde d_F(P,Q)$.
--
--   This is the first constant-factor approximation of the Fréchet distance in near-linear time for arbitrary curves; previous constant-factor algorithms ran in strongly subquadratic but not near-linear time, and under SETH no strongly subquadratic algorithm approximates within a factor below $3$.
--
--   **Formalization Note** Programs run on the mission's real RAM (`Machine`): the `SmaleNinth` core with `sqrt`, `idx` and `ofPtr`, rational literals, unit cost; input $p[0]=n$, $p[1]=m$ and the coordinates of $P$ then $Q$ in $M[0],M[1],\dots$; output $\hat D=M[-1]$ on `accept`. $f$ is chosen before $\varepsilon$; the programs and $C$ may depend on $d$ and $\varepsilon$ but not on $n,m$ or the coordinates.
--
--   Differences from the source:
--   - reading: "a deterministic algorithm … computes in $O(n^{1+\varepsilon})$ time a value $\hat D$" → an admissible program on the mission's real RAM that, on every input with $1\le m\le n$, accepts within $C\,n^{1+\varepsilon}$ steps with $\hat D$ in $M[-1]$; reason: the paper names no machine; $O(\cdot)$ is read as a worst-case bound with a constant depending on $d$ and $\varepsilon$ only
--   - reading: "The same guarantee holds for the discrete Fréchet distance" → a second program $\tilde A$ with the same $f$ and the same $C$; reason: the stronger reading (one $f$ for both), which the proof gives ($f(1/\varepsilon)=2D_K$ for both, p. 34 and Theorem B.1)
--   - encoding: $f:(0,\infty)\to[1,\infty)$ → $f:\mathbb R\to\mathbb R$ with $1\le f(x)$ for all $x>0$; reason: only values at $1/\varepsilon>0$ are used
--   - encoding: parameterizations not moving backwards along the curves → continuous nondecreasing parameter maps onto $[0,n-1]$ and $[0,m-1]$; reason: the paper's own parameterization over $[0,n-1]$ (p. 3); same matchings
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 2, Theorem 1.1 (proved §7.2, p. 34)

import Mathlib
import Definitions.Def_FrechetNearLinear_Main_Frechet
import Definitions.Def_FrechetNearLinear_Main_Machine

namespace FrechetNearLinear.Main

/-- Theorem 1.1 (Main result), p. 2. For every dimension `d ≥ 1` there is `f` with `f x ≥ 1`
for `x > 0` such that for every `ε > 0` there are admissible programs `A` (for `d_F`) and `Ã`
(for `d̃_F`) and a constant `C` such that, on every input `P ∈ (ℝ^d)^n`, `Q ∈ (ℝ^d)^m` with
`1 ≤ m ≤ n`, each program accepts within `C · n^{1+ε}` steps with an output `D̂` in `M[-1]`
satisfying `dist ≤ D̂ ≤ f(1/ε) · dist`. -/
theorem theorem_1_1 :
    ∀ d : ℕ, 1 ≤ d →
      ∃ f : ℝ → ℝ, (∀ x : ℝ, 0 < x → 1 ≤ f x) ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ A Adisc : Program, Admissible A ∧ Admissible Adisc ∧
            ∃ C : ℝ,
              ∀ n m : ℕ, 1 ≤ m → m ≤ n →
                ∀ (P : Fin n → E d) (Q : Fin m → E d),
                  (∃ Dhat : ℝ,
                    ComputesWithin A (curveInput P Q) (C * (n : ℝ) ^ (1 + ε)) Dhat ∧
                    frechetDist P Q ≤ Dhat ∧ Dhat ≤ f (1 / ε) * frechetDist P Q) ∧
                  (∃ Dhat : ℝ,
                    ComputesWithin Adisc (curveInput P Q) (C * (n : ℝ) ^ (1 + ε)) Dhat ∧
                    discreteFrechetDist P Q ≤ Dhat ∧
                    Dhat ≤ f (1 / ε) * discreteFrechetDist P Q) := by sorry

end FrechetNearLinear.Main
