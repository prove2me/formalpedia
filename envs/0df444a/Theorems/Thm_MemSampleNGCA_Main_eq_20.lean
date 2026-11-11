-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_eq_20
-- name    : MemSampleNGCA.Main.eq_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:42:13.771475+00:00
-- url     : https://prove2.me/theorems/5c276f66-b58e-494e-8ead-16a368f65071
-- title:
--   §B.1, Eq. (20) — λ_{i+1,v′}(θ) = E_0[λ_{i,V_i}(θ) · (dP_θ/dP_0)(X_{i+1}) | V_{i+1} = v′]
-- statement:
--   In the setting of Theorem B.1, let $\lambda_{i,v}(\theta)=P_\theta(V_i=v)/\nu_i(v)$ be the likelihood of the parameter $\theta$ at memory state $v$ after $i$ samples. For every $0\le i<N$, every state $v'$ with $\nu_{i+1}(v')>0$ and every $\theta\in\Theta$,
--   $$\lambda_{i+1,v'}(\theta)=\mathbb E_0\Big[\lambda_{i,V_i}(\theta)\cdot\frac{dP_\theta}{dP_0}(X_{i+1})\ \Big|\ V_{i+1}=v'\Big],$$
--   where $\mathbb E_0$ is the law of the run with samples i.i.d. from $P_0$.
--
--   The identity shows how the likelihoods propagate through one step of the algorithm. It motivates the definition of the truncated likelihoods $\Lambda_{i,v}$ (proved in §B.1.1).
--
--   Differences from the source:
--   - generalization: π is the uniform measure on Θ ⊆ S^{d−1} → π is any probability measure on a measurable space Θ; reason: π does not enter the identity beyond the setting; the uniform measure is an instance
--   - generalization: the setting of Theorem B.1 includes q ≥ 2 and h ≥ 1 → no hypotheses on q, h; reason: q and h do not occur in (20)
--   - encoding: a family {P_θ} with 0 ≤ dP_θ/dP_0 ≤ M → IsBoundedDensityFamily π P_0 p M; reason: as in Lemma B.2
--   - encoding: Definition 1.7 → StreamingAlg; reason: as in Lemma B.2
--   - encoding: E_0[Y | V_{i+1} = v′] → E_0[Y · 1{V_{i+1} = v′}] / ν_{i+1}(v′) (condOnEvent), stated for ν_{i+1}(v′) ≠ 0; reason: the conditional expectation given an event is defined exactly when it has positive probability
--   - encoding: iteration i ∈ ℕ → 0 ≤ i < N; reason: X_{i+1} exists only for i < N in a run on N samples
--   - encoding: λ real → λ in ℝ≥0∞ with λ_{i,v} = 0 when ν_i(v) = 0; reason: then P_θ(V_i = v) = 0 as well (P_θ ≪ P_0) and such states have probability 0 under E_0, so they do not affect the identity
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 17 (PDF 19), §B.1, Eq. (20); proof §B.1.1, p. 22 (PDF 24)

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming
import Definitions.Def_MemSampleNGCA_Main_Framework

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- §B.1, Eq. (20) (p. 17, PDF 19; proved in §B.1.1, p. 22): the likelihood
`λ_{i,v}(θ) = P_θ(V_i = v)/ν_i(v)` propagates as
`λ_{i+1,v'}(θ) = E₀[λ_{i,V_i}(θ) · (dP_θ/dP₀)(X_{i+1}) | V_{i+1} = v']`,
for every state `v'` with `ν_{i+1}(v') > 0`. -/
theorem eq_20 {Θ : Type*} [MeasurableSpace Θ] {X : Type*} [MeasurableSpace X]
    {B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Θ) (P₀ : Measure X) (p : Θ → X → ℝ) (M : ℝ)
    (hF : IsBoundedDensityFamily π P₀ p M)
    (A : StreamingAlg B X Ω) (N i : ℕ) (hi : i < N) (v' : Fin B → Bool)
    (hv' : nu A N P₀ (i + 1) v' ≠ 0) (θ : Θ) :
    lam A N P₀ p (i + 1) v' θ =
      condOnEvent (A.sampleLaw N P₀) {ω | A.state ω.1 ω.2 (i + 1) = v'}
        (fun ω => lam A N P₀ p i (A.state ω.1 ω.2 i) θ * ENNReal.ofReal (p θ (ω.1 ⟨i, hi⟩))) := by sorry

end MemSampleNGCA.Main
