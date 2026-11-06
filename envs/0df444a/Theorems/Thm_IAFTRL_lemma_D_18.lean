-- Prove2me | Theorems.Thm_IAFTRL_lemma_D_18
-- name    : IAFTRL.lemma_D_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:59.477564+00:00
-- url     : https://prove2.me/theorems/0865ee5e-51c4-49ef-83fd-5f0242affc48
-- title:
--   Lemma D.18 — actual-comparator regret decomposition (D.167)
-- statement:
--   Consider an execution of IA-FTRL for $T$ rounds, a vector $\theta\in\mathbb R^d$ with an action $a^*$, loss gaps $\Delta(a)=(a-a^*)^\top\theta$, corruptions $c^{\mathrm{vec}}_t=\theta_t-\theta$, and a comparator distribution $u$ on $\mathcal A$. With $g_{t,a}=(a-r_t)^\top v_{t,A_t}Y_t$, $H(q)=-\sum_aq_a\log q_a$, the mixability gap $D_t$ and the proxy function $C_t$,
--   $$
--   \mathrm{Reg}_T(u)=\mathbb E\Big[\sum_{t=1}^T\langle q_t-u,g_t\rangle\Big]+\sum_{t=1}^T\mathbb E[\langle p_t-q_t,\Delta\rangle]+\sum_{t=1}^T\mathbb E\Big[\sum_a(p_{t,a}-q_{t,a})a^\top c^{\mathrm{vec}}_t\Big]
--   $$
--   $$
--   \le\beta_1\log K+\sum_{t=2}^T(\beta_t-\beta_{t-1})\mathbb E[H(q_t)]+\sum_{t=1}^T\mathbb E[D_t]+\sum_{t=1}^T\mathbb E[\langle p_t-q_t,\Delta\rangle]+\sum_{t=1}^T\mathbb E\Big[\sum_a(p_{t,a}-q_{t,a})a^\top c^{\mathrm{vec}}_t\Big]
--   $$
--   $$
--   \le\beta_1\log K+\sum_{t=2}^T(\beta_t-\beta_{t-1})\mathbb E[H(q_t)]+\sum_{t=1}^T\mathbb E[C_t(p_t)]+\sum_{t=1}^T\mathbb E[\langle p_t-q_t,\Delta\rangle]+\sum_{t=1}^T\mathbb E\Big[\sum_a(p_{t,a}-q_{t,a})a^\top c^{\mathrm{vec}}_t\Big].
--   $$
--   The four terms are the penalty, stability, exploration and direct-corruption contributions bounded in Appendices D.2–D.5.
--
--   **Formalization Note** Rounds are 0-based: the paper's $\sum_{t=1}^T$ is a sum over Lean rounds $t<T$, and $\sum_{t=2}^T(\beta_t-\beta_{t-1})\mathbb E[H(q_t)]$ is $\sum_{1\le t<T}(\beta_{t+1}-\beta_t)\mathbb E[H(q_t)]$ with the Lean $q_t$ equal to the paper's $q_{t+1}$. The comparator distribution is identified with its mean action.
--
--   Differences from the source:
--   - generalization: corrupted stochastic regime with the unique optimal action $a^*$ and budget $C$ → any $\theta\in\mathbb R^d$ and any reference action $a_{j^*}$; no budget; reason: the decomposition only uses $\sum_a(p_{t,a}-q_{t,a})=0$; specializes to the source
--   - encoding: comparator distribution $u\in\mathcal P(\mathcal A)$ → probability vector $u$, regret against its mean action $\sum_au_aa$; reason: $\mathrm{Reg}_T(u)$ is linear in the comparator
--   - encoding: paper rounds $t=1,\dots,T$ → 0-based Lean rounds $t<T$, Lean round $t$ using $\beta_{t+1}$, $q_{t+1}$, $Z_{t+1}$; reason: Lean indexing convention; same instances
--   - encoding: dimension $d$ of $\mathbb R^d$ → $d\ge1$; reason: the paper works in $\mathbb R^d$ with a spanning action set in the unit ball; only the degenerate $d=0$ is excluded
--   - reading: protocol $\mathbb E[Y_t\mid\mathcal F_{t-1},\theta_t,A_t]=A_t^\top\theta_t$, $A_t\sim p_t$ → action law given $\mathcal G_t$, feedback identity given $\mathcal G_t\vee\sigma(A_t)$, for the pre-action filtration $\mathcal G_t$; reason: Appendix J.1, p.204: "Enlarging the pre-action filtration to include an environment\'s fresh pre-action randomization does not reveal it to the learner"
--   - reading: IA-FTRL with "a fixed $\mathcal F_{t-1}$-measurable rule" for $p_t$ → every $\mathcal F_{t-1}$-measurable minimizer of (2.3); reason: p.17 leaves the rule open ("e.g., the lexicographically smallest"); the lemma uses only feasibility of $p_t$
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix D.6.4, Lemma D.18, pp.91–92, Eq. (D.167)

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_Run_mixGap
import Definitions.Def_IAFTRL_proxyC
import Definitions.Def_IAFTRL_regretDist

namespace IAFTRL

open Matrix MeasureTheory

/-- **Lemma D.18 (Actual-comparator scalar regret decomposition).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma D.18, p.91:
"For a fixed comparator distribution `u ∈ 𝒫(𝒜)`, the actual corrupted regret satisfies (D.167)."
(D.167), p.92:
`Reg_T(u) = E[Σ_{t=1}^T ⟨q_t − u, g_t⟩] + Σ_t E[⟨p_t − q_t, Δ⟩] + Σ_t E[Σ_a (p_{t,a} − q_{t,a})a^⊤c^{vec}_t]`
`≤ β_1 log K + Σ_{t=2}^T (β_t − β_{t−1})E[H(q_t)] + Σ_t E[D_t] + Σ_t E[⟨p_t − q_t, Δ⟩] + Σ_t E[Σ_a (p_{t,a} − q_{t,a})a^⊤c^{vec}_t]`
`≤ β_1 log K + Σ_{t=2}^T (β_t − β_{t−1})E[H(q_t)] + Σ_t E[C_t(p_t)] + Σ_t E[⟨p_t − q_t, Δ⟩] + Σ_t E[Σ_a (p_{t,a} − q_{t,a})a^⊤c^{vec}_t]`.

For every execution of IA-FTRL for `T` rounds, every vector `θ` with an action `a* = a_{jstar}`, and
every comparator distribution `u` on the actions, with `Δ(a) = (a − a*)^⊤θ`, `c^{vec}_t = θ_t − θ`,
`g_{t,a} = (a − r_t)^⊤v_{t,A_t}Y_t`, `H(q) = −Σ_a q_a log q_a`, the mixability gap `D_t` of Lemma J.2 and
the proxy function `C_t`, the regret `Reg_T(u) = E[Σ_t (A_t − Σ_a u_a a)^⊤θ_t]` satisfies the identity
and the two inequalities of (D.167).

**Formalization Note.** Rounds are 0-based: the paper's `Σ_{t=1}^T` is `Σ_{t<T}`, the paper's
`Σ_{t=2}^T (β_t − β_{t−1})E[H(q_t)]` is `Σ_{t∈[1,T)} (β_{t+1} − β_t)E[H(q_t)]` with the Lean `q_t` being
the paper's `q_{t+1} = qSoft β_{t+1} arms (Σ_{s<t} θ̂_s)`. The decomposition holds for any `θ` and any
reference index `jstar`; the corrupted regime (unique `a*`, budget `C`) is not needed for it. -/
theorem lemma_D_18 {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (θ : Fin d → ℝ) (jstar : Fin K)
    (u : Fin K → ℝ) (hu0 : ∀ a, 0 ≤ u a) (hu1 : ∑ a, u a = 1) :
    let q : ℕ → Ω → Fin K → ℝ := fun t ω => qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω)
    let H : (Fin K → ℝ) → ℝ := fun p => -∑ a, p a * Real.log (p a)
    let explo : ℝ := ∑ t ∈ Finset.range T,
      ∫ ω, ∑ a, (R.p t ω a - q t ω a) * ((arms a - arms jstar) ⬝ᵥ θ) ∂P
    let corr : ℝ := ∑ t ∈ Finset.range T,
      ∫ ω, ∑ a, (R.p t ω a - q t ω a) * (arms a ⬝ᵥ (R.θs t ω - θ)) ∂P
    let pen : ℝ := beta d K 1 * Real.log K +
      ∑ t ∈ Finset.Ico 1 T, (beta d K (t + 1) - beta d K t) * ∫ ω, H (q t ω) ∂P
    regretDist P arms T R u =
        (∫ ω, ∑ t ∈ Finset.range T, ∑ a, (q t ω a - u a) * R.gEst arms t a ω ∂P) + explo + corr ∧
      regretDist P arms T R u ≤
        pen + ∑ t ∈ Finset.range T, ∫ ω, R.mixGap arms t ω ∂P + explo + corr ∧
      regretDist P arms T R u ≤
        pen + ∑ t ∈ Finset.range T, ∫ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ∂P +
          explo + corr := by sorry

end IAFTRL
