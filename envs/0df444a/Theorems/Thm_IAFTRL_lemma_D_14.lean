-- Prove2me | Theorems.Thm_IAFTRL_lemma_D_14
-- name    : IAFTRL.lemma_D_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:41.623916+00:00
-- url     : https://prove2.me/theorems/05544189-21dc-47a8-b76f-b1a284fe85cc
-- title:
--   Lemma D.14 — direct corruption contribution $\le16\sqrt2\,c_R\sqrt C$
-- statement:
--   Consider an execution of IA-FTRL for $T$ rounds in the corrupted stochastic regime with fixed loss vector $\theta$ ($\|\theta\|_{\mathcal A}\le1$) and deterministic budget $C\ge0$, i.e. $\sum_{t\le T}\|\theta_t-\theta\|_{\mathcal A}\le C$ almost surely. Let $a^*$ be an action, $c^{\mathrm{vec}}_t=\theta_t-\theta$, $e_{t,a}=(a-a^*)^\top c^{\mathrm{vec}}_t$ and $c_R=\sqrt{d\log(eK)}$. Then
--   $$
--   I_4:=\sum_{t=1}^T\mathbb E[\langle p_t-q_t,e_t\rangle]\le\sum_{t=1}^T\mathbb E\Big[\Big|\sum_a(p_{t,a}-q_{t,a})a^\top c^{\mathrm{vec}}_t\Big|\Big]\le16\sqrt2\,c_R\sqrt C .
--   $$
--
--   The exploration perturbation $p_t-q_t$ pays only $O(\sqrt{d\log K}\sqrt C)$ against an adaptive corruption, independently of $T$.
--
--   **Formalization Note** Rounds are 0-based; the Lean $q_t$ is the paper's $q_{t+1}$.
--
--   Differences from the source:
--   - generalization: $a^*$ the unique optimal action → any action $a_{j^*}$; reason: the bound uses only $\sum_a(p_{t,a}-q_{t,a})=0$; specializes to the source
--   - encoding: paper rounds $t=1,\dots,T$ → 0-based Lean rounds $t<T$, Lean round $t$ using $\beta_{t+1}$, $q_{t+1}$, $Z_{t+1}$; reason: Lean indexing convention; same instances
--   - encoding: dimension $d$ of $\mathbb R^d$ → $d\ge1$; reason: the paper works in $\mathbb R^d$ with a spanning action set in the unit ball; only the degenerate $d=0$ is excluded
--   - reading: protocol $\mathbb E[Y_t\mid\mathcal F_{t-1},\theta_t,A_t]=A_t^\top\theta_t$, $A_t\sim p_t$ → action law given $\mathcal G_t$, feedback identity given $\mathcal G_t\vee\sigma(A_t)$, for the pre-action filtration $\mathcal G_t$; reason: Appendix J.1, p.204: "Enlarging the pre-action filtration to include an environment\'s fresh pre-action randomization does not reveal it to the learner"
--   - reading: IA-FTRL with "a fixed $\mathcal F_{t-1}$-measurable rule" for $p_t$ → every $\mathcal F_{t-1}$-measurable minimizer of (2.3); reason: p.17 leaves the rule open ("e.g., the lexicographically smallest"); the lemma uses only feasibility of $p_t$
--   - reading: corrupted regime: fixed $\theta$ → fixed $\theta$ with $\|\theta\|_{\mathcal A}\le1$; reason: the stochastic regime\'s assumption (p.5), used in the corrupted regime as $0\le\kappa_t\le2$ (p.86)
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix D.5, Lemma D.14, p.86

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_qSoft

namespace IAFTRL

open Matrix MeasureTheory

/-- **Lemma D.14 (Direct corruption contribution).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma D.14, p.86: "For
`e_{t,a} = (a − a*)^⊤c^{vec}_t`,
`I_4 := Σ_{t=1}^T E[⟨p_t − q_t, e_t⟩] ≤ Σ_{t=1}^T E[|Σ_a (p_{t,a} − q_{t,a})a^⊤c^{vec}_t|] ≤ 16√2 c_R √C`."

For every execution of IA-FTRL for `T` rounds in the corrupted stochastic regime with fixed loss
vector `θ` (`‖θ‖_𝒜 ≤ 1`) and deterministic budget `C ≥ 0` (`Σ_{t<T} ‖θ_t − θ‖_𝒜 ≤ C` a.s.), every action
index `jstar`, with `c^{vec}_t = θ_t − θ` and `c_R = √(d log(eK))`:
`Σ_t E[⟨p_t − q_t, e_t⟩] ≤ Σ_t E[|Σ_a (p_{t,a} − q_{t,a})a^⊤c^{vec}_t|] ≤ 16√2 c_R √C`.

**Formalization Note.** Rounds are 0-based; the Lean `q_t` is the paper's `q_{t+1}`. The
inequalities hold for any reference index `jstar` (the paper's `a*`); uniqueness of `a*` is not used. -/
theorem lemma_D_14 {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (θ : Fin d → ℝ) (jstar : Fin K) (C : ℝ)
    (hC : 0 ≤ C) (hcor : IsCorrupted P arms θ C T R) :
    let q : ℕ → Ω → Fin K → ℝ := fun t ω => qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω)
    (∑ t ∈ Finset.range T,
        ∫ ω, ∑ a, (R.p t ω a - q t ω a) * ((arms a - arms jstar) ⬝ᵥ (R.θs t ω - θ)) ∂P) ≤
      ∑ t ∈ Finset.range T,
        ∫ ω, |∑ a, (R.p t ω a - q t ω a) * (arms a ⬝ᵥ (R.θs t ω - θ))| ∂P ∧
    (∑ t ∈ Finset.range T,
        ∫ ω, |∑ a, (R.p t ω a - q t ω a) * (arms a ⬝ᵥ (R.θs t ω - θ))| ∂P) ≤
      16 * Real.sqrt 2 * cR d K * Real.sqrt C := by sorry

end IAFTRL
