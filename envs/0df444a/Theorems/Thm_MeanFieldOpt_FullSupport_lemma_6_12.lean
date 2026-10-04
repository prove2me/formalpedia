-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_lemma_6_12
-- name    : MeanFieldOpt.FullSupport.lemma_6_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:11:19.783209+00:00
-- url     : https://prove2.me/theorems/aec7575c-d1ec-4afb-bfe2-ebd6846fbaf5
-- title:
--   Lemma 6.12 — after the support ends, $X_t$ has a density bounded below on compacts
-- statement:
--   Let $\xi$ be a mixture that is not identically zero, $f_0$ an admissible terminal condition, and $\gamma \in \mathscr L$ with $\gamma(t) = 0$ for all $t \in (t_1, 1)$, where $0 \le t_1 < 1$. Let $X$ be the strong solution of the SDE (6.3) for $\gamma$, driven by a standard Brownian motion. Then:
--
--   1. for every $t_* \in (t_1, 1)$ the law of $X_{t_*}$ has a density $p_{t_*}$ with respect to Lebesgue measure;
--   2. for every $t_* \in (t_1, 1)$ and every $M \ge 0$ there is $\varepsilon = \varepsilon(t_*, M, \gamma) > 0$ such that
--   $$
--   \inf_{|x| \le M,\ t \in [t_*, 1]} p_t(x) \ge \varepsilon .
--   $$
--
--   The lower bound on the density is what turns the strict Jensen inequality in the proof of the main theorem into a contradiction.
--
--   **Formalization Note** A density is defined only up to null sets, so claim 2 is stated without choosing versions: $\varepsilon\,\mathrm{Leb}(A) \le \mathbb P(X_t \in A)$ for every measurable $A \subseteq [-M, M]$ and every $t \in [t_*, 1]$. Given absolute continuity, this is equivalent to the existence of densities $p_t \ge \varepsilon$ on $[-M,M]$. Claim 1 is absolute continuity of the image measure $\mathbb P \circ X_{t_*}^{-1}$. The restriction $t_1 \ge 0$ is implicit in the paper ($\gamma$ lives on $[0,1)$; for $t_1 < 0$ claim 1 fails at $t_* = 0$, where $X_0 = 0$). The hypothesis that some $c_k \neq 0$ is added: for $\xi \equiv 0$, $X \equiv 0$ has no density.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 29, Lemma 6.12

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiSDE

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldOpt.FullSupport

/-- Lemma 6.12 (arXiv:2001.00904v1, p. 29): if `γ ∈ ℒ` vanishes on `(t₁, 1)`, `0 ≤ t₁ < 1`, then
for `t_* ∈ (t₁, 1)` the law of `X_{t_*}` has a Lebesgue density, and for every `M ≥ 0` there is
`ε > 0` with `inf_{|x| ≤ M, t ∈ [t_*, 1]} p_t(x) ≥ ε`, stated without choosing density versions:
`ε · Leb(A) ≤ P(X_t ∈ A)` for every measurable `A ⊆ [-M, M]` and `t ∈ [t_*, 1]`.
Added (disclosed) hypothesis: the mixture is not identically zero. -/
theorem lemma_6_12 (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀)
    (γ : ℝ → ℝ) (hγ : InL ξ γ) (t₁ : ℝ) (ht₁ : 0 ≤ t₁) (ht₁' : t₁ < 1)
    (hzero : ∀ t ∈ Set.Ioo t₁ 1, γ t = 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W X : ℝ≥0 → Ω → EthierKurtz.SDEState 1) (hW : IsBrownianReal (fun t ω => W t ω 0) P)
    (hX : IsParisiSDESol ξ f₀ γ P W X) :
    (∀ ts ∈ Set.Ioo t₁ 1, P.map (pathAt X ts) ≪ volume) ∧
    ∀ ts ∈ Set.Ioo t₁ 1, ∀ M : ℝ, 0 ≤ M → ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Icc ts 1, ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (-M) M →
        ENNReal.ofReal ε * volume A ≤ P.map (pathAt X t) A := by sorry

end MeanFieldOpt.FullSupport
