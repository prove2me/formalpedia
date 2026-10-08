-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_lemma_3
-- name    : KhachiyanRound.BCD.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:26.391986+00:00
-- url     : https://prove2.me/theorems/b1022c17-af85-40f9-a845-ba44ab4d4e43
-- title:
--   Lemma 3, p. 312 — BCD iterates satisfy F₀ > −∞, ε₀ ≤ m − 1, (2.21) and (2.22)
-- statement:
--   Let $\mathcal A = \{a_1,\dots,a_m\} \subset \mathbb{R}^n$, $n \ge 2$, be centrally symmetric (2.1) and full-dimensional (2.2), and let $p_0, p_1, \dots$ be any run of the barycentric coordinate descent method (BCD). Write $F_k = F(p_k)$, $\varepsilon_k = \varepsilon(p_k)$ and $F^*$ for the optimal value of (2.3). Then every iterate lies in $S_F$, and
--
--   1. (2.20) $F_0 > -\infty$ (i.e. $\det A(p_0) > 0$) and $\varepsilon_0 \le m - 1$;
--   2. (2.21) for every $k$,
--   $$\Delta_k = F_{k+1} - F_k \ge \ln(1+\varepsilon_k) - \frac{\varepsilon_k}{1+\varepsilon_k};$$
--   3. (2.22) for every $k$, $\delta_k = F^* - F_k \le n\ln(1+\varepsilon_k)$.
--
--   Each BCD step increases the objective by an amount controlled by the current accuracy, while the remaining gap is bounded by the same accuracy; the iteration count of Lemma 4 follows from these two facts.
--
--   **Formalization Note** The conjunct "every $p_k \in S_F$" makes explicit what the page's "$F_k$" presupposes ($F_k > -\infty$); without it Lean's $F_k$ could be the junk value $\ln 0 = 0$. The run allows any maximizing index $r$ at every step.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 312, Lemma 3, (2.20)–(2.22)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem lemma_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (hsymm : IsCentrallySymmetric a) (hfull : affineSpan ℝ (Set.range a) = ⊤) (hn : 2 ≤ n)
    (p : ℕ → ι → ℝ) (hrun : IsBCDRun a p) :
    (∀ k, p k ∈ SF a) ∧
    (0 < (momentMatrix a (p 0)).det ∧ epsOf a (p 0) ≤ (Fintype.card ι : ℝ) - 1) ∧
    (∀ k, Real.log (1 + epsOf a (p k)) - epsOf a (p k) / (1 + epsOf a (p k)) ≤
      F a (p (k + 1)) - F a (p k)) ∧
    (∀ k, Fstar a - F a (p k) ≤ (n : ℝ) * Real.log (1 + epsOf a (p k))) := by sorry
end KhachiyanRound.BCD
