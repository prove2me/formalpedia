-- Prove2me | Theorems.Thm_JacodTodorov10_LLN_lemma_8_1_consistency
-- name    : JacodTodorov10.LLN.lemma_8_1_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:20:41.149923+00:00
-- url     : https://prove2.me/theorems/91d9278a-76b4-4628-aab7-56cd6d81148a
-- title:
--   Lemma 8.1, (8.18) — ĉ(kₙ)ᵢ → c_S and ĉ(kₙ)_{i−kₙ−1} → c_{S−} in probability away from big jumps
-- statement:
--   Assume (H-$r$) with $r<2$, (K-$v$), the localized bound (8.3) with function $\gamma$, and (3.3). Let $m\ge0$, let $S$ be an $\mathcal F^{(m)}_0$-measurable positive finite time and, for each $n$, let $i_n\ge1$ be an $\mathcal F^{(m)}_0$-measurable random integer. Then
--   $$\widehat c(k_n)_{i_n}\xrightarrow{\ \mathbb P\ }c_S\quad\text{on }\Omega(m,n,S,i_n)_+,\qquad \widehat c(k_n)_{i_n-k_n-1}\xrightarrow{\ \mathbb P\ }c_{S-}\quad\text{on }\Omega(m,n,S,i_n)_-,$$
--   that is, for every $\eta>0$,
--   $$\mathbb P\big(\Omega(m,n,S,i_n)_+\cap\{|\widehat c(k_n)_{i_n}-c_S|>\eta\}\big)\to0,\qquad \mathbb P\big(\Omega(m,n,S,i_n)_-\cap\{|\widehat c(k_n)_{i_n-k_n-1}-c_{S-}|>\eta\}\big)\to0.$$
--
--   The local estimators computed on the window just after (respectively before) a time $S$ recover the volatility just after (respectively before) $S$, provided no big jump falls in that window. Applied at $S=T_p$, this gives the convergence of each summand of $\widetilde U^n(m)$ in (8.27).
--
--   **Formalization Note** "Convergence in probability on $\Omega_n$" is read as above, with the $n$-dependent sets. The random integer depends on $n$, because the sets require $(i-1)\Delta_n<S\le i\Delta_n$. $\mathcal F^{(m)}_0=\mathcal F_0\vee\mathcal G_m$. Only the last assertion (8.18) of Lemma 8.1 is formalized; it needs (3.3) only, not (8.15).
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §8.2, Lemma 8.1, (8.18), p. 29; the sets Ω(m, n, S, i)±, p. 28

import Mathlib
import Definitions.Def_JacodTodorov10_LLN_Local

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- **Lemma 8.1, (8.18)** of Jacod–Todorov, *Do price and volatility jump together?*,
arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §8.2, pp. 28–29: assume (H-r) with `r < 2`, (K-v),
(8.3) and (3.3). Let `m ≥ 0`, let `S` be an `𝓕^{(m)}_0`-measurable positive finite time and, for
each `n`, `i_n ≥ 1` an `𝓕^{(m)}_0`-measurable random integer. Then
`ĉ(k_n)_{i_n} → c_S` in probability on `Ω(m, n, S, i_n)_+` and
`ĉ(k_n)_{i_n−k_n−1} → c_{S−}` in probability on `Ω(m, n, S, i_n)_−`, that is, for every `η > 0`,
`P(Ω(m, n, S, i_n)_+ ∩ {|ĉ(k_n)_{i_n} − c_S| > η}) → 0` and
`P(Ω(m, n, S, i_n)_− ∩ {|ĉ(k_n)_{i_n−k_n−1} − c_{S−}| > η}) → 0`.

Formalization Note: "→^P on Ω_n" is read as convergence in probability restricted to the
`n`-dependent sets. The random integer depends on `n`, since the sets require
`(i − 1)Δ_n < S ≤ iΔ_n`. `D_m` is the set of big-jump times `Dm` (empty for `m = 0`), and
`𝓕^{(m)}_0 = 𝓕_0 ∨ 𝒢_m` (`Fm`). The sets may be non-measurable a priori; `P` is then the outer
measure. -/
theorem lemma_8_1_consistency {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (lam : Measure E) [SigmaFinite lam] (M : Data Ω E) (r v C : ℝ) (Γ : ℝ≥0 → Ω → ℝ)
    (γ γhat : E → ℝ) (Sc : Scheme) (ϖ ρ : ℝ)
    (hM : IsModel 𝓕 P lam M) (hH : HAssume 𝓕 P lam r M) (hr : r < 2)
    (hK : KAssume 𝓕 P lam v M) (hB : Bdd83 lam M r v C Γ γ γhat) (hS : Sc.Cond33 ϖ ρ)
    (m : ℕ) (S : Ω → ℝ≥0) (hSmeas : Measurable[Fm 𝓕 M.N γ m 0] S) (hSpos : ∀ ω, 0 < S ω)
    (i : ℕ → Ω → ℤ) (himeas : ∀ n, Measurable[Fm 𝓕 M.N γ m 0] (i n))
    (hipos : ∀ n ω, 1 ≤ i n ω) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n => P (OmegaPlus Sc M.N γ m n S (i n) ∩
        {ω | η < |Sc.chat M.X n (i n ω) ω - c M.σ (S ω) ω|})) atTop (𝓝 0) ∧
    Tendsto (fun n => P (OmegaMinus Sc M.N γ m n S (i n) ∩
        {ω | η < |Sc.chat M.X n (i n ω - Sc.k n - 1) ω - cLeft M.σ (S ω) ω|})) atTop (𝓝 0) := by sorry

end JacodTodorov10.LLN
