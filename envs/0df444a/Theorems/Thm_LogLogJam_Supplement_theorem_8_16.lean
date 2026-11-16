-- Prove2me | Theorems.Thm_LogLogJam_Supplement_theorem_8_16
-- name    : LogLogJam.Supplement.theorem_8_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:55:19.192986+00:00
-- url     : https://prove2.me/theorems/0eaa77f7-8ee8-469d-9260-238fd65f4436
-- title:
--   Theorem 8.16 — single-copy (non-Gaussian) measurements learn pure single-mode Gaussian states with $O(\log(1/\delta)/\varepsilon^2)$ copies
-- statement:
--   There is an absolute constant $C>0$ such that for every $0<\varepsilon\le1/3$, $0<\delta<1$ and every number of copies
--
--   $$
--   m\ \ge\ \frac{C\log(1/\delta)}{\varepsilon^2}
--   $$
--
--   there is a learning protocol that measures each of the $m$ copies separately with a fixed (nonadaptive) POVM and then post-processes the outcomes, such that for every pure single-mode Gaussian state $\rho=\rho(0,V)$ with zero displacement it outputs, with probability at least $1-\delta$, a pure Gaussian state $\rho(0,\hat V)$ with zero displacement and
--
--   $$
--   D_{\mathrm{tr}}\big(\rho(0,V),\rho(0,\hat V)\big)\le\varepsilon .
--   $$
--
--   So for one mode neither entanglement across copies nor adaptivity is needed to escape the energy dependence that Theorem 1.1 forces on Gaussian measurements; the protocol uses non-Gaussian measurements (the canonical phase POVM and photon counting).
--
--   Differences from the source:
--
--   - generalization: a learning protocol on $m=C\log(1/\delta)/\varepsilon^2$ copies → a protocol on every integer number $m\ge C\log(1/\delta)/\varepsilon^2$ of copies; reason: the printed $m$ is in general not an integer; the Lean statement specializes to $m=\lceil C\log(1/\delta)/\varepsilon^2\rceil$
--   - generalization: a learning protocol that uses single-copy measurements → a nonadaptive single-copy scheme (the published `BosonicLearn.AdaptiveScheme 1 m ℝ` whose POVMs do not depend on earlier outcomes), with real outcomes, followed by a randomized estimator (a Markov kernel to density operators); reason: Theorem 1.5 (p.3) describes this protocol as nonadaptive, and the proof (p.59) applies the canonical phase POVM and photon counting to fixed copies, with real outcomes; a nonadaptive scheme with real outcomes is a single-copy protocol, so the Lean statement implies the source's
--   - encoding: outputs a description of a pure Gaussian state $\rho(0,\hat V)$ → the estimate $\sigma$ is a density operator, and success requires $\sigma$ to be a pure centered Gaussian state with $D_{\mathrm{tr}}(\rho,\sigma)\le\varepsilon$; reason: a description of a state is the state; same instances
--   - encoding: a pure (zero-displacement) Gaussian state $\rho(0,V)$ → $\rho(0,V_K)$ for some $K$ in the Siegel disk $\mathfrak D_n$ (`IsPureCentGauss`); reason: §4.4 (pp.18–19) and Lemma 4.6: the pure centered $n$-mode Gaussian states are exactly the $|\psi_K\rangle\langle\psi_K|$, $K\in\mathfrak D_n$, with covariance $V_K$; same instances
--   - encoding: the Gaussian state $\rho(m,V)$ with $V_{ij}=\mathrm{Tr}(\rho\{\hat R_i-m_i,\hat R_j-m_j\})$ (vacuum $V=I$), quadratures $(q_1,\dots,q_n,p_1,\dots,p_n)$ → a density operator on $\ell^2(\mathbb N^n)$ satisfying the published `BosonicLearn.IsGaussianState` with mean $m$ and covariance $V/2$, indices reindexed from $\mathrm{Fin}\,2\times\mathrm{Fin}\,n$ to $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$; reason: `IsGaussianState` uses $\Sigma=\tfrac12\mathrm{Tr}(\rho\{\cdot,\cdot\})$ (vacuum $\tfrac12 I$) with the same $\hat q,\hat p$ and grouped order; its extra clauses (finite energy, symmetry, moment identities) hold for every Gaussian state; same instances
--   - encoding: probabilities as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals, measures); reason: every quantity is a nonnegative integral or a probability; same values
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Theorem 8.16, p.53 (PDF p.56); Theorem 1.5, p.3 (PDF p.6); proof p.59 (PDF p.62)

import Mathlib
import Definitions.Def_LogLogJam_Supplement_IsGaussQP
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_traceDist

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

open LogLogJam

/-- **Theorem 8.16** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…,
Theorem 8.16, p.53, PDF p.56): "There is an absolute constant C > 0 such that for any
0 < ε ⩽ 1/3, and 0 < δ < 1, there is a learning protocol that uses single-copy measurements on
m = C log(1/δ)/ε² copies of an unknown pure single-mode Gaussian state ρ(0, V), and outputs a
description of a pure Gaussian state ρ(0, V̂) such that Dtr(ρ(0, V), ρ(0, V̂)) ⩽ ε with
probability at least 1 − δ."

There is an absolute `C > 0` such that for every `ε ∈ (0, 1/3]`, `δ ∈ (0, 1)` and every number of
copies `m ≥ C log(1/δ)/ε²` there are a nonadaptive single-copy measurement scheme on `m` copies
(real outcomes) and a randomized estimator such that, for every pure centered single-mode Gaussian
state `ρ`, the output `σ` is a pure centered Gaussian state with `D_tr(ρ, σ) ≤ ε` with probability at
least `1 − δ`.

**Formalization Note** The printed `m = C log(1/δ)/ε²` is read as every integer `m` at least
this value. Nonadaptivity (`S.povm t` independent of the earlier outcomes) is Theorem 1.5's
description of this protocol (p.3); the outcome space is `ℝ` (canonical-phase angles and photon
counts are real). -/
theorem theorem_8_16 :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 3 → 0 < δ → δ < 1 →
      ∀ m : ℕ, C * Real.log (1 / δ) / ε ^ 2 ≤ m →
      ∃ (S : BosonicLearn.AdaptiveScheme 1 m ℝ)
        (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
        (∀ (t : Fin m) (x x' : Fin t → ℝ), S.povm t x = S.povm t x') ∧
        IsMarkovKernel est ∧
        ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
          ENNReal.ofReal (1 - δ) ≤
            ∫⁻ x, est x {σ | IsPureCentGauss σ ∧
                BosonicLearn.traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε}
              ∂(BosonicLearn.transcriptLaw S ρ.coefficients) := by sorry

end LogLogJam.Supplement
