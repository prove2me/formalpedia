-- Prove2me | Theorems.Thm_JacodTodorov10_LLN_eq_8_4
-- name    : JacodTodorov10.LLN.eq_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:20:52.616178+00:00
-- url     : https://prove2.me/theorems/18ba0b83-e12e-4fee-93d9-8aab54204c3b
-- title:
--   (8.4) — the big jumps separate: P(Ω_{n,t,m}) → 1
-- statement:
--   Assume (H-$r$), (K-$v$), the localized bound (8.3) with function $\gamma$, and (3.3). Fix an integer $m\ge1$ and a time $t$. Let $D_m$ be the set of times of the atoms $(s,z)$ of $\mu$ with $\gamma(z)>1/m$, and let $\Omega_{n,t,m}$ be the event that any two distinct times $T\ne T'$ in $D_m$ satisfy
--   $$T>t,\quad\text{or}\quad T>3k_n\Delta_n\ \text{ and }\ |T-T'|>6k_n\Delta_n.$$
--   Then
--   $$\lim_{n\to\infty}\mathbb P(\Omega_{n,t,m})=1.$$
--
--   On $\Omega_{n,t,m}$ the big jumps up to time $t$ lie in distinct sampling windows, away from time $0$; this lets the proof of Theorem 3.1 treat each big jump separately.
--
--   **Formalization Note** The page enumerates the big jumps as $(T_p)_{p\in\mathcal T_m}$; here $D_m=\{T_p:p\in\mathcal T_m\}$, since $\bigcup_{m'\le m}\{1/m'<\gamma\le1/(m'-1)\}=\{\gamma>1/m\}$, and distinct indices give distinct times because $\mu$ has at most one atom at each time.
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §8.1, (8.4), p. 25

import Mathlib
import Definitions.Def_JacodTodorov10_LLN_Local

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- **(8.4)** of Jacod–Todorov, *Do price and volatility jump together?*, arXiv:1010.4990v1
(Ann. Appl. Probab. 20 (2010)), §8.1, p. 25: under the standing assumptions (H-r), (K-v), (8.3) of
§8 and (3.3), for every integer `m ≥ 1` and every `t`, `P(Ω_{n,t,m}) → 1` as `n → ∞`, where
`Ω_{n,t,m}` is the event that any two distinct big-jump times `T_p ≠ T_q`, `p, q ∈ 𝒯_m` (jumps of
`μ` with `γ(z) > 1/m`), satisfy `T_p > t`, or `T_p > 3k_nΔ_n` and `|T_p − T_q| > 6k_nΔ_n`.

Formalization Note: the enumeration `(T_p)` of the big jumps is not formalized; `{T_p : p ∈ 𝒯_m}`
is the set `Dm` of times of the atoms `(s, z)` of `μ` with `γ(z) > 1/m`, since
`⋃_{m' ≤ m} {1/m' < γ ≤ 1/(m'−1)} = {γ > 1/m}` (reading `1/0` as `+∞`). Distinct indices give
distinct times because `μ` has at most one atom at each time (`IsFPoisson`). `γ` is the function of
(8.3), which also satisfies (H-r)(c). -/
theorem eq_8_4 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (lam : Measure E) [SigmaFinite lam] (M : Data Ω E) (r v C : ℝ) (Γ : ℝ≥0 → Ω → ℝ)
    (γ γhat : E → ℝ) (S : Scheme) (ϖ ρ : ℝ)
    (hM : IsModel 𝓕 P lam M) (hH : HAssume 𝓕 P lam r M) (hK : KAssume 𝓕 P lam v M)
    (hB : Bdd83 lam M r v C Γ γ γhat) (hS : S.Cond33 ϖ ρ) (m : ℕ) (hm : 1 ≤ m) (t : ℝ≥0) :
    Tendsto (fun n => P (OmegaNTM S M.N γ n t m)) atTop (𝓝 1) := by sorry

end JacodTodorov10.LLN
