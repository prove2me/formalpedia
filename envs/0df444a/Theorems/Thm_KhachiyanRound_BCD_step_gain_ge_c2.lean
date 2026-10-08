-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_step_gain_ge_c2
-- name    : KhachiyanRound.BCD.step_gain_ge_c2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:05.045977+00:00
-- url     : https://prove2.me/theorems/d5590947-d0c1-468a-b8ea-c5013a4c21a9
-- title:
--   (2.27), p. 313 — if ε_k ≥ 1 then c₂ ≤ Δ_k ≤ δ_k, c₂ = ln 2 − 1/2
-- statement:
--   Under the assumptions of Lemma 3, with $\Delta_k = F(p_{k+1}) - F(p_k)$, $\delta_k = F^* - F(p_k)$ and $c_2 = \ln 2 - \tfrac12 > 0$: for every $k$ with $\varepsilon_k \ge 1$,
--   $$c_2 \le \Delta_k \le \delta_k .$$
--
--   An iteration with accuracy at least $1$ gains at least the constant $c_2$, which can only happen while the gap is at least $c_2$; combined with (2.25) and $\delta_0 \le n\ln m$ this bounds the number of such iterations.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 313, (2.27), proof of Lemma 4

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem step_gain_ge_c2 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a : ι → Fin n → ℝ)
    (hsymm : IsCentrallySymmetric a) (hfull : affineSpan ℝ (Set.range a) = ⊤) (hn : 2 ≤ n)
    (p : ℕ → ι → ℝ) (hrun : IsBCDRun a p) :
    ∀ k : ℕ, 1 ≤ epsOf a (p k) →
      Real.log 2 - 1 / 2 ≤ F a (p (k + 1)) - F a (p k) ∧
        F a (p (k + 1)) - F a (p k) ≤ Fstar a - F a (p k) := by sorry
end KhachiyanRound.BCD
