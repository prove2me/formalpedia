-- Prove2me | Theorems.Thm_NewtonLCP_theorem_1_2
-- name    : NewtonLCP.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:32:44.298986+00:00
-- url     : https://prove2.me/theorems/1d918e4f-1d1b-41a5-ab90-5071c35533c4
-- title:
--   Theorem 1.2 — Algorithm 3 solves sufficient LCPs with $O(\min\{\sqrt n(1+\hat\kappa),n^{9/8}\sqrt{1+\hat\kappa}\}(L+\log(2+\hat\kappa)))$ Newton solves
-- statement:
--   Let $M\in\mathcal P_\star\cap\mathbb Q^{n\times n}$ and $q\in\mathbb Q^n$ of total encoding length $L$. There exists an algorithm that either finds a solution to LCP$(M,q)$ or concludes its infeasibility in total running time dominated by
--
--   $$O\Big(\min\big\{\sqrt n\,(1+\hat\kappa(M)),\ n^{9/8}\sqrt{1+\hat\kappa(M)}\big\}\cdot\big(L+\log(2+\hat\kappa(M))\big)\Big)$$
--
--   many linear system solves, and in addition $O(\log(2+\hat\kappa(M)))$ linear programs of the form $Mx+q=s$, $x,s\ge0_n$, $x_I=0_I$, $s_J=0_J$ for some $I,J\subseteq[n]$.
--
--   The statement is about Algorithm 3 itself: there are constants $C_1,C_2$ (lines 17–18) and $C>0$ such that for every parameter choice allowed by (54), every $n$, every rational $M\in\mathcal P_\star$ and $q$, and every correct LP oracle,
--
--   1. Algorithm 3 returns a solution of LCP$(M,q)$, or returns "infeasible" and LCP$(M,q)$ has no solution;
--   2. the number of Newton linear-system solves is at most $C\min\{\sqrt n(1+\hat\kappa(M)),n^{9/8}\sqrt{1+\hat\kappa(M)}\}(L+\log(2+\hat\kappa(M)))$;
--   3. the number of LP calls is at most $C\log(2+\hat\kappa(M))$.
--
--   This is the first improvement of the handicap dependence of interior point methods for sufficient LCPs from linear to square root; the algorithm needs no knowledge of $\hat\kappa(M)$.
--
--   **Formalization Note** Logarithms are natural; $L$ is the sum of the bit sizes of the entries of $M$ and $q$; all arithmetic of the algorithm is exact real arithmetic.
--
--   Differences from the source:
--   - generalization: there exists an algorithm → the statement is about Algorithm 3 itself, for every parameter choice allowed by (54) and every correct LP oracle, with ∃ C₁, C₂ (the 'appropriately chosen constants' of lines 17–18); reason: it specializes to the existence claim
--   - reading: total running time dominated by k linear system solves → at most k Newton-system solves, counted at lines 5 and 9 of Algorithm 3; LP calls counted at lines 15 and 28; reason: the paper measures time in these units and gives no cost model for the O(n) vector work between solves
--   - reading: O(·) → one absolute constant C > 0, uniform in n, M, q, the oracle and the parameter choice, for both bounds; natural logarithm; reason: the bounds are claimed for all inputs with one hidden constant
--   - encoding: total encoding length L → Σ bitSize of the entries of M and q (published bitSize); reason: any standard encoding is within constant factors
--   - encoding: an LP solver → an arbitrary oracle meeting the LP specification (IsLPOracle), universally quantified; reason: any LP solver meets the specification
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Theorem 1.2, p.3 (restated p.31; proof pp.31–33)

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_Params
import Definitions.Def_NewtonLCP_Algorithm3

namespace NewtonLCP

/-- **Theorem 1.2** (main result). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 1.2, p.3 (restated p.31; proof pp.31–33).

Let `M ∈ P⋆ ∩ ℚⁿˣⁿ`, `q ∈ ℚⁿ` of total encoding length `L`. There exists an algorithm that
either finds a solution to LCP(M, q) or concludes its infeasibility in total running time
dominated by `O(min{√n(1 + κ̂(M)), n^{9/8}√(1 + κ̂(M))} · (L + log(2 + κ̂(M))))` many linear
system solves, and in addition the running time of `O(log(2 + κ̂(M)))` linear programs of the
form `Mx + q = s, x, s ≥ 0ₙ, x_I = 0_I, s_J = 0_J` for some `I, J ⊆ [n]`.

**Formalization Note.** The algorithm is Algorithm 3 itself (`algorithm3`), with constants
`C₁, C₂` (lines 17–18) chosen once, for **every** parameter choice `β, δ` allowed by (54) and
**every** correct LP oracle `O`. Its result is `(outcome, solves, lps)`: `solves` counts the
Newton-system solves (lines 5, 9), `lps` the LP calls (lines 15, 28). The `O(·)` bounds are one
constant `C > 0`, uniform in `n, M, q, β, δ, O`. `L = encLen M q`; `log` is natural; `κ̂(M)` is
`handicap` of the real cast of `M`. -/
theorem theorem_1_2 : ∃ C₁ C₂ : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ β δ : ℕ → ℝ → ℝ, AdmissibleParams β δ →
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (q : Fin n → ℚ),
      IsPStar (M.map ((↑) : ℚ → ℝ)) →
      ∀ O : LPOracle n, IsLPOracle (M.map ((↑) : ℚ → ℝ)) (fun i => (q i : ℝ)) O →
        ((∃ x s, (algorithm3 C₁ C₂ β δ O M q).1 = Out.solution x s ∧
            IsLCPSol (M.map ((↑) : ℚ → ℝ)) (fun i => (q i : ℝ)) x s) ∨
          ((algorithm3 C₁ C₂ β δ O M q).1 = Out.infeasible ∧
            ¬ ∃ x s, IsLCPSol (M.map ((↑) : ℚ → ℝ)) (fun i => (q i : ℝ)) x s)) ∧
        ((algorithm3 C₁ C₂ β δ O M q).2.1 : ℝ) ≤
          C * min (Real.sqrt n * (1 + handicap (M.map ((↑) : ℚ → ℝ))))
                ((n : ℝ) ^ ((9 : ℝ) / 8) * Real.sqrt (1 + handicap (M.map ((↑) : ℚ → ℝ)))) *
            ((encLen M q : ℝ) + Real.log (2 + handicap (M.map ((↑) : ℚ → ℝ)))) ∧
        ((algorithm3 C₁ C₂ β δ O M q).2.2 : ℝ) ≤
          C * Real.log (2 + handicap (M.map ((↑) : ℚ → ℝ))) := by sorry

end NewtonLCP
