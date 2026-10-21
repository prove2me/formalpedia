-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_corollary_A1
-- name    : InterimTesting.NotProficient.corollary_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:37.533954+00:00
-- url     : https://prove2.me/theorems/44074810-76de-470b-8fa4-68c6648b04d0
-- title:
--   Corollary A1 a), c), p. A5 (PDF 31) — 𝒯1 is lower after a proficient formative result and non-increasing in first-period effort
-- statement:
--   Under the formative assessment, for either starting state $S_0$:
--
--   1. for every $e_0\in[0,1]$, $\ \mathcal T_1(P,e_0,S_0)\le\mathcal T_1(N,e_0,S_0)$;
--   2. for every observation $x\in\{P,N\}$ and $0\le e_0\le e_0'\le1$, $\ \mathcal T_1(x,e_0',S_0)\le\mathcal T_1(x,e_0,S_0)$.
--
--   That is, the second-period threshold decreases in the observed midyear level of proficiency and in the first-period effort.
--
--   **Formalization Note** Part b) of the corollary (monotonicity in $\mu$) is not formalized; Proposition 1's proof does not use it.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A5 (PDF 31), Corollary A1 a) and c)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Corollary A1 a) and c), p. A5: under the formative assessment, `𝒯1(S1)` is lower after a
proficient observation, `𝒯1(P, e0, S0) ≤ 𝒯1(N, e0, S0)`, and non-increasing in the first-period
effort `e0`. -/
theorem corollary_A1 (θ : Params) (hθ : θ.Standing) (S0 : Prof) :
    (∀ e0 ∈ Set.Icc (0 : ℝ) 1, T1 θ false S0 e0 .P ≤ T1 θ false S0 e0 .N) ∧
      (∀ (x : Prof), ∀ e ∈ Set.Icc (0 : ℝ) 1, ∀ e' ∈ Set.Icc (0 : ℝ) 1, e ≤ e' →
        T1 θ false S0 e' x ≤ T1 θ false S0 e x) := by sorry

end InterimTesting.NotProficient
