-- Prove2me | Theorems.Thm_MissionAbort_joint_convergence
-- name    : MissionAbort.joint_convergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:06.79351+00:00
-- url     : https://prove2.me/theorems/7b1e0fe7-159b-42a1-828c-078c09436363
-- title:
--   Appendix A.2: joint convergence of the times and the signals
-- statement:
--   Let $F,G$ be lifetime laws and $m_i(\lambda)/\lambda\to\infty$ for $i=1,2$. Let $T^{(\lambda)}$ have the law of independent $G^{(\lambda)}$, $\mathrm{Exp}(\zeta)$ and $F^{(\lambda)}$, and $T$ the law of independent $G$, $\mathrm{Exp}(\zeta)$ and $F$. Let the signals have, on both sides, the same conditional law given the times,
--   $$
--   \prod_{n=1}^N e\big(\mathrm{state}(u;n\delta),y_n\big).
--   $$
--   Then for every bounded continuous $f$ on $\mathbb R^3\times\{0,\dots,K\}^N$,
--   $$
--   \mathbb E\big[f(T^{(\lambda)},Y^{(\lambda)}_{1:N})\big]\longrightarrow\mathbb E\big[f(T,Y_{1:N})\big]\qquad(\lambda\to\infty),
--   $$
--   that is, $(T^{(\lambda)},Y^{(\lambda)}_{1:N})$ converges to $(T,Y_{1:N})$ in distribution.
--
--   This is the step that carries the convergence of the Erlang mixtures into the conditional laws given the signals. The kernel is discontinuous on a set that is null under the limit, because $F$ and $G$ have no atoms.
--
--   Differences from the source:
--   - generalization: $F,G$ with densities → $F,G$ with no atoms; reason: the proof uses only "the continuity assumption on $T_{12},T_{13},T_{23}$" (p.EC.3); laws with densities satisfy this
--   - encoding: $(T^{(\lambda)},Y^{(\lambda)}_{1:N})$ on $\Omega^{(\lambda)}$ → the law on $\mathbb R^3\times\{0,\dots,K\}^N$ built from the time law and the kernel, tested on bounded continuous functions; reason: the triple is not realized on $\Omega^{(\lambda)}$; the page writes the same integral on p.EC.2
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, pp.EC.2–EC.3, "converges to (T12, T13, T23, Y1:N) in distribution as λ → ∞"

import Mathlib
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_timeLaw
import Definitions.Def_MissionAbort_IsLifetimeLaw
import Definitions.Def_MissionAbort_erlangMix
import Definitions.Def_MissionAbort_jointExpectation

open MeasureTheory ProbabilityTheory Filter Topology

namespace MissionAbort

/-- **Joint convergence** (Sun, Hu & Ye, arXiv:2505.03225v1, Appendix A.2, p.EC.3, "converges to
`(T12, T13, T23, Y1:N)` in distribution as `λ → ∞`"). Let `T⁽λ⁾` have the law of independent
`G⁽λ⁾`, exponential of rate `ζ`, and `F⁽λ⁾`, and `T` the law of independent `G`, exponential of rate `ζ`,
and `F`. With the same signal kernel on both sides, `(T⁽λ⁾, Y⁽λ⁾_{1:N})` converges in distribution to
`(T, Y_{1:N})`.

**Formalization Note.** The surrogate triple has no canonical realization on `Ω⁽λ⁾`, so this is stated
for the laws on `ℝ³ × {0, …, K}ᴺ`, by bounded continuous test functions. The kernel is discontinuous
on a set that is null under the limit, because `F` and `G` have no atoms. -/
theorem joint_convergence {K : ℕ} (M : Model K) (F G : Measure ℝ) (hF : IsLifetimeLaw F)
    (hG : IsLifetimeLaw G) (m₁ m₂ : ℝ → ℕ)
    (hm₁ : Tendsto (fun lam => (m₁ lam : ℝ) / lam) atTop atTop)
    (hm₂ : Tendsto (fun lam => (m₂ lam : ℝ) / lam) atTop atTop)
    (f : BoundedContinuousFunction ((ℝ × ℝ × ℝ) × (Fin M.N → Fin (K + 1))) ℝ) :
    Tendsto
      (fun lam => jointExpectation M
        (timeLaw (erlangMix G (m₁ lam) (lam - M.ζ)) M.ζ (erlangMix F (m₂ lam) lam)) f)
      atTop (𝓝 (jointExpectation M (timeLaw G M.ζ F) f)) := by sorry

end MissionAbort
