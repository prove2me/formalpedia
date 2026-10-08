-- Prove2me | Theorems.Thm_GenEmpLik_Expansion_eq_32
-- name    : GenEmpLik.Expansion.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:48:08.109935+00:00
-- url     : https://prove2.me/theorems/c4d2bc58-73d3-47db-ae94-1d29aa267662
-- title:
--   (32) — the robust mean is sandwiched between suprema over $\mathcal U_{\rm sm}$ and $\mathcal U_{\rm big}$
-- statement:
--   Let $f$ satisfy Assumption A, $n\ge1$, $\rho>0$, $0<\epsilon<1$, $C\ge0$ with $C\epsilon<1$, and suppose the two inequalities of (30) hold at these $\epsilon$ and $C$:
--   $2(1-C\epsilon)h_\epsilon(t)\le f(t+1)$ for $t\ge-1$, and $f(t+1)\le(1+C\epsilon)t^2$ for $|t|\le\epsilon$. Then for every $z\in\mathbb R^n$, with $\mathcal U_{\rm sm},\mathcal U,\mathcal U_{\rm big}$ the sets of (31),
--
--   $$
--   \sup_{u\in\mathcal U_{\rm sm}}u^Tz\;\le\;\sup_p\Big\{p^Tz \;:\; D_f\big(p\,\|\,\tfrac1n\mathbb 1\big)\le\tfrac\rho n\Big\}-\frac1n\mathbb 1^Tz\;=\;\sup_{u\in\mathcal U}u^Tz\;\le\;\sup_{u\in\mathcal U_{\rm big}}u^Tz .
--   $$
--
--   The middle term is the robust mean minus the sample mean. This reduces the expansion of the robust mean to the two explicit optimisation problems over $\mathcal U_{\rm sm}$ and $\mathcal U_{\rm big}$.
--
--   **Formalization Note** The paper takes $C$ from (30) with $\epsilon\le c$; here the two inequalities at the given $\epsilon$ and $C$ are hypotheses, which is what the proof uses. The suprema are real `sSup`s; the sets of values are non-empty ($0\in\mathcal U_{\rm sm}$) and bounded above under the hypotheses, so they are true suprema. The sample mean $\frac1n\mathbb 1^Tz$ is the published `empMean`.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 32, App. A.1, (31) and (32)

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_AssumptionA
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_GenEmpLik_Expansion_reparamSets
import Definitions.Def_VarianceRegularization_Expansion_empMean

open VarianceRegularization.Expansion

namespace GenEmpLik.Expansion

/-- (32) (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 32): if the two inequalities of (30)
hold at `ε` and `C` (with `0 < ε < 1`, `0 ≤ C`, `Cε < 1`), then for every `z ∈ ℝⁿ`
`sup_{u ∈ 𝒰_sm} uᵀz ≤ sup_p {pᵀz | D_f(p ‖ 𝟙/n) ≤ ρ/n} − (1/n)𝟙ᵀz = sup_{u ∈ 𝒰} uᵀz
  ≤ sup_{u ∈ 𝒰_big} uᵀz`. -/
theorem eq_32 (f : ℝ → EReal) (hA : AssumptionA f) {n : ℕ} (hn : 0 < n) {ρ ε C : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 ≤ C) (hCε : C * ε < 1)
    (hlow : ∀ t : ℝ, -1 ≤ t → ((2 * (1 - C * ε) * huber ε t : ℝ) : EReal) ≤ f (t + 1))
    (hup : ∀ t : ℝ, |t| ≤ ε → f (t + 1) ≤ (((1 + C * ε) * t ^ 2 : ℝ) : EReal))
    (z : Fin n → ℝ) :
    sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Usm n ε C ρ) ≤
        robustMean f ρ z - empMean z ∧
      robustMean f ρ z - empMean z =
        sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Umid f n ρ) ∧
      sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Umid f n ρ) ≤
        sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Ubig n ε C ρ) := by sorry

end GenEmpLik.Expansion
