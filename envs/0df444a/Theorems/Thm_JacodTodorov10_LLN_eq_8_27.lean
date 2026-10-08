-- Prove2me | Theorems.Thm_JacodTodorov10_LLN_eq_8_27
-- name    : JacodTodorov10.LLN.eq_8_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:20:37.653817+00:00
-- url     : https://prove2.me/theorems/9e0db4a1-ccb7-44f2-a17e-6f58b6e77573
-- title:
--   (8.27) — the big-jump part Ũⁿ(m) converges in probability (Skorokhod) to Ũ(m)
-- statement:
--   Assume (H-$r$) with $r<2$, (K-$v$), the localized bound (8.3) with function $\gamma$, and (3.3), and let $F$ be a Borel function on $\mathbb R^3$ which is continuous at each point of $R\times(0,\infty)^2$ for some $R\in\mathcal R$. For every integer $m\ge1$, with $D_m$ the set of big-jump times and $i(n,s)=\lceil s/\Delta_n\rceil$, the processes
--   $$\widetilde U^n(m)_t=\sum_{s\in D_m,\ s\le\Delta_n[t/\Delta_n]}F\big(\Delta^n_{i(n,s)}X,\ \widehat c(k_n)_{i(n,s)-k_n-1},\ \widehat c(k_n)_{i(n,s)}\big)\,1_{\{|\Delta^n_{i(n,s)}X|>u_n\}}$$
--   converge in probability, for the Skorokhod topology, to
--   $$\widetilde U(m)_t=\sum_{s\in D_m,\ s\le t}F(\Delta X_s,c_{s-},c_s)\,1_{\{\Delta X_s\neq0\}}.$$
--
--   This is the first step of the proof of Theorem 3.1: the part of $U(F,k_n)$ coming from the finitely many big jumps converges to the corresponding part of $U(F)$.
--
--   **Formalization Note** The page sums over $p\in\mathcal T_m$; the sums here run over the times $s\in D_m$. The display (8.27) drops the factor $1_{\{\Delta X_{T_p}\neq0\}}$ that the sentence before it has; it is kept. None of the cases (a)–(c) of Theorem 3.1 is assumed. Convergence in probability for the Skorokhod topology is the subsequence criterion.
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §8.4, step 1, (8.25)–(8.27), p. 33

import Mathlib
import Definitions.Def_JacodTodorov10_LLN_Local

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- **(8.27)** of Jacod–Todorov, *Do price and volatility jump together?*, arXiv:1010.4990v1
(Ann. Appl. Probab. 20 (2010)), §8.4, step 1, p. 33: assume (H-r) with `r < 2`, (K-v), (8.3) and
(3.3), and let `F` be a Borel function continuous at each point of `R × ℝ*₊²` for some `R ∈ 𝓡`.
For every `m ≥ 1`, the big-jump part
`Ũ^n(m)_t = ∑_{p ∈ 𝒯_m(n,t)} F(Δ^n_{i(n,p)} X, ĉ(k_n, p−), ĉ(k_n, p+)) 1_{|Δ^n_{i(n,p)} X| > u_n}`
of `U(F, k_n)` converges in probability, for the Skorokhod topology, to
`Ũ(m)_t = ∑_{p ∈ 𝒯_m} F(ΔX_{T_p}, c_{T_p−}, c_{T_p}) 1_{ΔX_{T_p} ≠ 0} 1_{T_p ≤ t}`.

Formalization Note: the sums run over the big-jump times `s ∈ D_m` instead of the enumeration
`(T_p)`, with `i(n, s) = ⌈s/Δ_n⌉`. The limit keeps the factor `1_{ΔX_{T_p} ≠ 0}` of the sentence
before (8.27), which the display drops. No case (a)–(c) of Theorem 3.1 is assumed: the step does not
use it. Convergence in probability for the Skorokhod topology is `TendstoInProbJ1`. -/
theorem eq_8_27 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (lam : Measure E) [SigmaFinite lam] (M : Data Ω E) (r v C : ℝ) (Γ : ℝ≥0 → Ω → ℝ)
    (γ γhat : E → ℝ) (S : Scheme) (ϖ ρ : ℝ) (F : ℝ → ℝ → ℝ → ℝ)
    (hM : IsModel 𝓕 P lam M) (hH : HAssume 𝓕 P lam r M) (hr : r < 2)
    (hK : KAssume 𝓕 P lam v M) (hB : Bdd83 lam M r v C Γ γ γhat) (hS : S.Cond33 ϖ ρ)
    (hFmeas : Measurable (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2))
    (hFcont : ∃ R : Set ℝ, InR P M.X R ∧ ∀ x ∈ R, ∀ y z : ℝ, 0 < y → 0 < z →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) (x, y, z))
    (m : ℕ) (hm : 1 ≤ m) :
    TendstoInProbJ1 P (fun n => Utilde S M.X M.N γ F m n) (Ulim M.X M.σ M.N γ F m) := by sorry

end JacodTodorov10.LLN
