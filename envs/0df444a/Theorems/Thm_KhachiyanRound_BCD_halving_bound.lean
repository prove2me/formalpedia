-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_halving_bound
-- name    : KhachiyanRound.BCD.halving_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:39.353139+00:00
-- url     : https://prove2.me/theorems/4ea96605-920b-40c7-a8eb-d1eae1fc73f2
-- title:
--   p. 314 — if ε_k ≤ 1, halving ε_k takes h(ε_k) ≤ n/(c₃ε_k) iterations, c₃ = ln(3/2) − 1/3
-- statement:
--   Under the assumptions of Lemma 3, let $c_3 = \ln(3/2) - \tfrac13 > 0$ and suppose $\varepsilon_k \le 1$. If $h$ is a number of iterations such that $\varepsilon_{k+i} > \varepsilon_k/2$ for every $i < h$, then
--   $$h \le \frac{n}{c_3\,\varepsilon_k}.$$
--   In particular the number $h(\varepsilon_k) = \min\{h \mid \varepsilon_{k+h} \le \varepsilon_k/2\}$ of iterations needed to halve $\varepsilon_k$ is at most $n/(c_3\varepsilon_k)$.
--
--   Summing these bounds over successive halvings gives the second phase $H(\varepsilon) = O(n/\varepsilon)$ of the iteration bound (2.23).
--
--   **Formalization Note** The page bounds $h(\varepsilon_k)$, a minimum that is a priori over a possibly empty set; the Lean statement bounds every $h$ before the first halving, which implies both that the minimum exists and the page's bound.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 314, bound on h(ε_k), proof of Lemma 4

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem halving_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a : ι → Fin n → ℝ)
    (hsymm : IsCentrallySymmetric a) (hfull : affineSpan ℝ (Set.range a) = ⊤) (hn : 2 ≤ n)
    (p : ℕ → ι → ℝ) (hrun : IsBCDRun a p) :
    ∀ k : ℕ, epsOf a (p k) ≤ 1 → ∀ h : ℕ,
      (∀ i < h, epsOf a (p k) / 2 < epsOf a (p (k + i))) →
        (h : ℝ) ≤ (n : ℝ) / ((Real.log (3 / 2) - 1 / 3) * epsOf a (p k)) := by sorry
end KhachiyanRound.BCD
