-- Prove2me | Theorems.Thm_IAFTRL_lemma_D_1
-- name    : IAFTRL.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:15.263453+00:00
-- url     : https://prove2.me/theorems/e6d4b091-109e-4800-b9a3-70c83fc0e9ae
-- title:
--   Lemma D.1 — attainment, measurable lexicographic selection, integrability
-- statement:
--   Let $\mathcal A$ be a finite action set in the unit ball of $\mathbb R^d$ ($d\ge1$) spanning $\mathbb R^d$.
--   1. For every round $t\ge1$ and every cumulative estimate $S\in\mathbb R^d$, the program (2.3) has a minimizer.
--   2. For every $t\ge1$ there is a Borel measurable map $S\mapsto\mathrm{sel}(S)$ such that, for every $S$, $\mathrm{sel}(S)$ minimizes (2.3) and is lexicographically smallest (in the fixed action order) among all minimizers; in particular it is unique.
--   3. For every execution of IA-FTRL for $T$ rounds on a probability space, the estimates $\hat\theta_t$ ($t<T$) and the action-loss differences $\hat L_{a}-\hat L_{c}=(a-c)^\top\sum_{s<t}\hat\theta_s$ ($t\le T$, all actions $a,c$) are integrable.
--
--   This makes the optimization step a well-defined measurable decision rule and justifies the expectations in the analysis.
--
--   **Formalization Note** The history enters (2.3) only through $S=\sum_{s<t}\hat\theta_s$, so Borel measurability in $S$ composed with the measurable map from the history to $S$ is Borel measurability in the history. The lexicographic order is `toLex` on `Fin K → ℝ`.
--
--   Differences from the source:
--   - encoding: "Borel measurable in the history" → Borel measurable in $S=\sum_{s<t}\hat\theta_s$; reason: the program depends on the history only through $S$ ("Borel in $\sum_{s=1}^{t-1}\hat\theta_s$", p.66); composition with history $\mapsto S$
--   - encoding: "uniquely defined" → $\mathrm{sel}(S)$ is the least minimizer in the linear order `toLex`; reason: uniqueness of a least element of a linear order
--   - reading: "covariance estimates and action-loss differences" → $\hat\theta_t$ and $(a-c)^\top\sum_{s<t}\hat\theta_s$; reason: the quantities bounded in (D.14)–(D.16)
--   - generalization: integrability for the lexicographic rule → integrability for every execution (any $\mathcal F_{t-1}$-measurable minimizer, any environment of the protocol); reason: the bounds (D.14)–(D.16) use only feasibility; specializes to the lexicographic rule
--   - encoding: $\mathbb R^d$, rounds $t\ge1$ → $d\ge1$, $t\ge1$; reason: the paper's setting
--   - reading: protocol $\mathbb E[Y_t\mid\mathcal F_{t-1},\theta_t,A_t]=A_t^\top\theta_t$, $A_t\sim p_t$ → action law given $\mathcal G_t$, feedback identity given $\mathcal G_t\vee\sigma(A_t)$, for the pre-action filtration $\mathcal G_t$; reason: Appendix J.1, p.204: "Enlarging the pre-action filtration to include an environment\'s fresh pre-action randomization does not reveal it to the learner"
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix D.1.2, Lemma D.1, p.65

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsMin2_3
import Definitions.Def_IAFTRL_IsIAFTRLRun

namespace IAFTRL

open Matrix MeasureTheory

/-- **Lemma D.1 (Attainment and measurable sampling-law selection).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma D.1, p.65:
"On every finite history, the objective in (2.3), with `v = v(p)` prescribed by
`M(p) = Σ_{a∈𝒜} p_a aa^⊤` and `v_a(p) = M(p)^{-1}a`, attains its minimum over `p`. The
lexicographically least minimizing `p_t`, in the fixed action ordering, is uniquely defined and
Borel measurable in the history. For every fixed finite horizon, its covariance estimates and
action-loss differences are integrable."

For a spanning finite action set in the unit ball of `ℝ^d` (`d ≥ 1`):
1. for every paper round `t ≥ 1` and every cumulative estimate `S`, program (2.3) has a minimizer;
2. for every `t ≥ 1` there is a Borel map `S ↦ sel(S)` such that `sel(S)` is, for every `S`, the
   lexicographically least minimizer of (2.3) (in the order of `Fin K`);
3. for every execution of IA-FTRL on a probability space, every horizon `T` and every round, the
   estimates `θ̂_t` (`t < T`) and the action-loss differences `L̂_{t,a} − L̂_{t,c}` (`t ≤ T`) are
   integrable.

**Formalization Note.** The history enters (2.3) only through `S = Σ_{s<t} θ̂_s` (p.56; "Borel in
`Σ_{s=1}^{t−1} θ̂_s`", p.66); composing `sel` with the measurable map history ↦ `S` gives Borel
dependence on the history. Uniqueness of the lexicographically least minimizer is the
antisymmetry of the linear order `toLex`. Clause 3 is stated for every run, i.e. for any
`F_{t−1}`-measurable minimizer, since the bounds (D.14)–(D.16) use only feasibility. -/
theorem lemma_D_1 {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms) :
    (∀ t : ℕ, 1 ≤ t → ∀ S : Fin d → ℝ, ∃ p : Fin K → ℝ, IsMin2_3 arms t S p) ∧
    (∀ t : ℕ, 1 ≤ t → ∃ sel : (Fin d → ℝ) → (Fin K → ℝ), Measurable sel ∧
      ∀ S, IsMin2_3 arms t S (sel S) ∧
        ∀ p : Fin K → ℝ, IsMin2_3 arms t S p → toLex (sel S) ≤ toLex p) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
      (R : Run d K Ω), IsIAFTRLRun P arms T R →
      (∀ t < T, Integrable (R.thetaHat arms t) P) ∧
      ∀ t ≤ T, ∀ a c : Fin K,
        Integrable (fun ω => arms a ⬝ᵥ R.cumEst arms t ω - arms c ⬝ᵥ R.cumEst arms t ω) P) := by sorry

end IAFTRL
