-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_lemma_C_3
-- name    : LinearMDPRL.Misspec.lemma_C_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:06.186128+00:00
-- url     : https://prove2.me/theorems/fcb11f41-7ca3-4117-afd8-0bd1352c8e8c
-- title:
--   Lemma C.3, p. 21 — with β_k = c_β(d√ι + ζ√(kd))H, P(𝔈) ≥ 1 − p/2 for an absolute C independent of c_β
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $c_\beta>0$. Let the MDP be $\zeta$-approximately linear with $d,H,K\ge1$, let $p\in(0,1)$, $T=KH$, $\iota=\log(2dT/p)$, and run LSVI-UCB with $\lambda=1$ and $\beta_k=c_\beta(d\sqrt\iota+\zeta\sqrt{kd})H$ against an adaptive choice of initial states. Let $\mathfrak E$ be the event
--   $$\forall(k,h)\in[K]\times[H]:\quad\Big\|\sum_{\tau=1}^{k-1}\phi^\tau_h\big[V^k_{h+1}(x^\tau_{h+1})-\mathbb P_hV^k_{h+1}(x^\tau_h,a^\tau_h)\big]\Big\|_{(\Lambda^k_h)^{-1}}\le C\cdot dH\sqrt\chi,\qquad\chi=\log[2(c_\beta+1)dT/p].$$
--   Then $\mathbb P(\mathfrak E)\ge1-p/2$.
--
--   This is the uniform concentration of the stochastic noise in the least-squares targets; $C$ does not depend on $c_\beta$, which is what allows Lemma C.5 to choose $c_\beta$ afterwards.
--
--   **Formalization Note** "With probability at least $1-p/2$" is written as: the (outer) measure of the complement of $\mathfrak E$ is at most $p/2$. The page says $p\in[0,1]$; at $p=0$, $\chi$ involves a division by zero, so $p\in(0,1)$ as in Theorem 3.2. $\|v\|_{\Lambda^{-1}}=\sqrt{v^\top\Lambda^{-1}v}$. The proof (via Lemma B.3) applies a uniform concentration bound to $V^k_{h+1}$, which requires $\sup_x|V^k_{h+1}(x)|\le H$; Algorithm 1 clips $Q^k$ only from above, so this is not automatic. The statement is formalized as printed.
-- source:
--   arXiv:1907.05388v2, Lemma C.3, p. 21 (proof p. 22, by Lemma B.3, p. 17)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP
import Definitions.Def_LinearMDPRL_Misspec_Event

open MeasureTheory ProbabilityTheory Matrix

namespace LinearMDPRL.Misspec

universe u v w

/-- **Lemma C.3** (p. 21). There is an absolute constant `C > 0`, independent of `c_β`, such that
for every `c_β > 0`, under the setting of Theorem 3.2 with `λ = 1` and
`β_k = c_β (d√ι + ζ√(kd)) H`, and every `p ∈ (0, 1)`, the event `𝔈` of `goodEvent` (with
`χ = log[2(c_β + 1) d T / p]`) fails with probability at most `p / 2`. -/
theorem lemma_C_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ cβ : ℝ, 0 < cβ →
    ∀ {S : Type u} {A : Type v} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
      [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
    ∀ (M : LinearMDPRL.Linear.EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ : ℝ),
      IsApproxLinearMDP M H d φ ζ →
    ∀ p : ℝ, 0 < p → p < 1 →
    ∀ {Ω : Type w} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝓕 : Filtration ℕ mΩ) (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A),
      LinearMDPRL.Linear.IsLSVIUCBRun μ 𝓕 M φ 1 (betaMis cβ ζ d H K p) H K x a →
      μ {ω | ¬ goodEvent M φ ζ C cβ p H K (fun τ i => x τ i ω) (fun τ i => a τ i ω)}
        ≤ ENNReal.ofReal (p / 2) := by sorry

end LinearMDPRL.Misspec
