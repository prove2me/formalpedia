-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lemma_B_3
-- name    : LinearMDPRL.Linear.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:46:27.339791+00:00
-- url     : https://prove2.me/theorems/7dc39dbc-2942-4bf9-b412-8739357270e6
-- title:
--   Lemma B.3, p. 17 — for an absolute constant C independent of c_β, the good event 𝔈 has probability ≥ 1 − p/2
-- statement:
--   Work in the setting of Theorem 3.1: a linear MDP (Assumption A) with $d,H,K\ge1$, LSVI-UCB run with $\lambda=1$ and $\beta=c_\beta\cdot dH\sqrt\iota$, $\iota=\log(2dT/p)$, $T=KH$, where $c_\beta>0$. There is an absolute constant $C>0$, independent of $c_\beta$, such that for every $p\in(0,1)$ the event $\mathfrak E$ that for all $(k,h)\in[K]\times[H]$
--   $$
--   \Big\|\sum_{\tau=1}^{k-1}\phi^\tau_h\big[V^k_{h+1}(x^\tau_{h+1})-\mathbb P_hV^k_{h+1}(x^\tau_h,a^\tau_h)\big]\Big\|_{(\Lambda^k_h)^{-1}}\le C\cdot dH\sqrt\chi,\qquad\chi=\log\big[2(c_\beta+1)dT/p\big],
--   $$
--   satisfies
--   $$
--   \mathbb P(\mathfrak E)\ge1-p/2 .
--   $$
--
--   This is the main concentration step of the analysis: the regression noise of least-squares value iteration is uniformly small, even though the regression targets $V^k_{h+1}$ depend on the data.
--
--   **Formalization Note.** The constant $C$ is chosen before $c_\beta$ and before the MDP, the dimensions and the run. The paper writes "for any fixed $p\in[0,1]$"; at $p=0$ the quantity $\chi$ is undefined, so $p\in(0,1)$ as in Theorem 3.1. The bound is stated as $\mu(\text{complement of }\mathfrak E)\le p/2$, an outer-measure bound.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma B.3, p. 17

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Linear_LinearMDP
import Definitions.Def_LinearMDPRL_Linear_ProofObjects

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory Matrix

/-- **Lemma B.3** (arXiv:1907.05388v2, p. 17). Under the setting of Theorem 3.1, let `c_β` be the
constant in `β = c_β · dH√ι`. There is an absolute constant `C`, independent of `c_β`, such that
for any fixed `p ∈ (0, 1)`, the event `𝔈` (`goodEvent`) that for all `(k, h) ∈ [K] × [H]`
`‖Σ_{τ=1}^{k-1} φ^τ_h [V^k_{h+1}(x^τ_{h+1}) − P_h V^k_{h+1}(x^τ_h, a^τ_h)]‖_{(Λ^k_h)^{-1}} ≤ C · dH√χ`,
`χ = log[2(c_β + 1)dT/p]`, has probability at least `1 − p/2`. -/
theorem lemma_B_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ cβ : ℝ, 0 < cβ →
      ∀ {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
        [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
      ∀ (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)), IsLinearMDP M H d φ →
      ∀ p : ℝ, 0 < p → p < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A),
        IsLSVIUCBRun μ 𝓕 M φ 1 (fun _ => cβ * d * H * Real.sqrt (iota d K H p)) H K x a →
        μ {ω | ¬ goodEvent M φ C cβ p H K (fun τ i => x τ i ω) (fun τ i => a τ i ω)}
          ≤ ENNReal.ofReal (p / 2) := by sorry

end LinearMDPRL.Linear
