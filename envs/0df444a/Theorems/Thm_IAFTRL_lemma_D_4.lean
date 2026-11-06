-- Prove2me | Theorems.Thm_IAFTRL_lemma_D_4
-- name    : IAFTRL.lemma_D_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:40.707306+00:00
-- url     : https://prove2.me/theorems/144a3054-90ca-4933-b764-8a52b82caac8
-- title:
--   Lemma D.4 — the proxy function bounds the conditional mixability gap
-- statement:
--   Consider an execution of IA-FTRL for $T$ rounds and a round $t<T$. Let $g_{t,a}=(a-r_t)^\top v_{t,A_t}Y_t$ and let
--   $$
--   D_t=\langle q_t,g_t\rangle+\beta_t\log\sum_aq_{t,a}e^{-g_{t,a}/\beta_t}
--   $$
--   be the entropy-FTRL mixability gap. Then $D_t$ is integrable and
--   $$
--   \mathbb E_{t-1}[D_t]\le C_t(p_t)\le\frac{2d}{\beta_t},
--   $$
--   the first inequality almost surely, with $\mathbb E_{t-1}$ the conditional expectation given the pre-action σ-algebra $\mathcal G_t$, and the second on every outcome.
--
--   The program's stability constraint therefore controls the stability term of FTRL.
--
--   **Formalization Note** Rounds are 0-based: the Lean round $t$ uses $\beta_{t+1}$, $q_{t+1}$ and $C_{t+1}$.
--
--   Differences from the source:
--   - reading: $\mathbb E_{t-1}$ → conditional expectation given the pre-action σ-algebra $\mathcal G_t$; reason: Appendix J.1 (p.204); $C_t(p_t)$ is $\mathcal F_{t-1}$-measurable, so the bound given $\mathcal F_{t-1}$ follows by the tower property
--   - encoding: conditional expectation of $D_t$ → integrability of $D_t$ added to the conclusion; reason: guards Lean's junk conditional expectation; true by Lemma D.1
--   - encoding: paper rounds $t=1,\dots,T$ → 0-based Lean rounds $t<T$, Lean round $t$ using $\beta_{t+1}$, $q_{t+1}$, $Z_{t+1}$; reason: Lean indexing convention; same instances
--   - encoding: dimension $d$ of $\mathbb R^d$ → $d\ge1$; reason: the paper works in $\mathbb R^d$ with a spanning action set in the unit ball; only the degenerate $d=0$ is excluded
--   - reading: protocol $\mathbb E[Y_t\mid\mathcal F_{t-1},\theta_t,A_t]=A_t^\top\theta_t$, $A_t\sim p_t$ → action law given $\mathcal G_t$, feedback identity given $\mathcal G_t\vee\sigma(A_t)$, for the pre-action filtration $\mathcal G_t$; reason: Appendix J.1, p.204: "Enlarging the pre-action filtration to include an environment\'s fresh pre-action randomization does not reveal it to the learner"
--   - reading: IA-FTRL with "a fixed $\mathcal F_{t-1}$-measurable rule" for $p_t$ → every $\mathcal F_{t-1}$-measurable minimizer of (2.3); reason: p.17 leaves the rule open ("e.g., the lexicographically smallest"); the lemma uses only feasibility of $p_t$
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix D.3.1, Lemma D.4, p.70

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_Run_mixGap
import Definitions.Def_IAFTRL_proxyC

namespace IAFTRL

open Matrix MeasureTheory

/-- **Lemma D.4 (Executed reconstruction and centered stability).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma D.4, p.70:
"For IA-FTRL, set `g_{t,a} = (a − r_t)^⊤v_{t,A_t}Y_t` and let `D_t` be the entropy-FTRL mixability gap.
Then `E_{t−1}[D_t] ≤ C_t(p_t) ≤ 2d/β_t`."

For every execution of IA-FTRL for `T` rounds and every round `t < T` (paper round `t + 1`), the
mixability gap `D_t = ⟨q_t, g_t⟩ + β_t log Σ_a q_{t,a} e^{−g_{t,a}/β_t}` of Lemma J.2:
1. is integrable;
2. satisfies `E[D_t | G_t] ≤ C_t(p_t)` a.s.;
3. and `C_t(p_t) ≤ 2d/β_t` holds on every outcome.

**Formalization Note.** `E_{t−1}` is conditioning on the pre-action σ-algebra `G_t` (p.204).
Integrability is stated so that the conditional expectation is not Mathlib's junk value. 0-based
round `t` uses `β_{t+1}`, `q_{t+1}` and `C_{t+1}`. -/
theorem lemma_D_4 {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t < T) :
    Integrable (R.mixGap arms t) P ∧
    P[R.mixGap arms t | R.G t] ≤ᵐ[P]
      (fun ω => proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω)) ∧
    ∀ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ≤ 2 * (d : ℝ) / beta d K (t + 1) := by sorry

end IAFTRL
