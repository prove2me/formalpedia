-- Prove2me | Theorems.Thm_LogLogJam_Supplement_theorem_8_3
-- name    : LogLogJam.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:54:20.485229+00:00
-- url     : https://prove2.me/theorems/345be49a-343f-4ddd-880a-fe4cd9dc65a3
-- title:
--   Theorem 8.3 — an entangled POVM learns pure $n$-mode Gaussian states with $O((n^2+\log(1/\delta))/\varepsilon^2)$ copies, independent of energy
-- statement:
--   There is an absolute constant $C>0$ such that for every $n\ge1$, $0<\varepsilon\le1$, $0<\delta<1$ and every number of copies
--
--   $$
--   m\ \ge\ \frac{C}{\varepsilon^2}\big(n^2+\log(1/\delta)\big)\qquad(25)
--   $$
--
--   there is a POVM $M$ on $m$ copies of the $n$-mode Fock space, whose outcomes are states, with the following property: for every pure $n$-mode Gaussian state $\rho=\rho(0,V)$ with zero displacement, measuring $\rho^{\otimes m}$ with $M$ yields, with probability at least $1-\delta$, a pure Gaussian state $\sigma=\rho(0,\hat V)$ with zero displacement such that
--
--   $$
--   D_{\mathrm{tr}}\big(\rho(0,V),\rho(0,\hat V)\big)\le\varepsilon .
--   $$
--
--   The number of copies does not depend on the energy of $\rho$: with non-Gaussian entangled measurements the energy dependence forced by Theorem 1.1 for Gaussian measurements disappears.
--
--   Differences from the source:
--
--   - generalization: a POVM on $m=\frac{C}{\varepsilon^2}(n^2+\log(1/\delta))$ copies → a POVM on every integer number $m\ge\frac{C}{\varepsilon^2}(n^2+\log(1/\delta))$ of copies; reason: the printed $m$ is in general not an integer; the Lean statement specializes to $m=\lceil\frac{C}{\varepsilon^2}(n^2+\log(1/\delta))\rceil$, and a POVM may ignore extra copies
--   - encoding: a POVM on $m$ copies whose outcome specifies a pure Gaussian state $\rho(0,\hat V)$ → a published `BosonicLearn.FockPOVM` on $\ell^2(\mathbb N^n)^{\otimes m}$ (index $\mathrm{Fin}\,m\to\mathbb N^n$) with outcomes in the density operators, applied to $\rho^{\otimes m}$ (`WildeQIT.Schumacher.tensorPow`); success requires the outcome $\sigma$ to be a pure centered Gaussian state and $D_{\mathrm{tr}}(\rho,\sigma)\le\varepsilon$; reason: a description of a state is the state; arbitrary (entangled, non-Gaussian) POVMs are allowed, as in §8.2; same instances
--   - encoding: a pure (zero-displacement) Gaussian state $\rho(0,V)$ → $\rho(0,V_K)$ for some $K$ in the Siegel disk $\mathfrak D_n$ (`IsPureCentGauss`); reason: §4.4 (pp.18–19) and Lemma 4.6: the pure centered $n$-mode Gaussian states are exactly the $|\psi_K\rangle\langle\psi_K|$, $K\in\mathfrak D_n$, with covariance $V_K$; same instances
--   - encoding: the Gaussian state $\rho(m,V)$ with $V_{ij}=\mathrm{Tr}(\rho\{\hat R_i-m_i,\hat R_j-m_j\})$ (vacuum $V=I$), quadratures $(q_1,\dots,q_n,p_1,\dots,p_n)$ → a density operator on $\ell^2(\mathbb N^n)$ satisfying the published `BosonicLearn.IsGaussianState` with mean $m$ and covariance $V/2$, indices reindexed from $\mathrm{Fin}\,2\times\mathrm{Fin}\,n$ to $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$; reason: `IsGaussianState` uses $\Sigma=\tfrac12\mathrm{Tr}(\rho\{\cdot,\cdot\})$ (vacuum $\tfrac12 I$) with the same $\hat q,\hat p$ and grouped order; its extra clauses (finite energy, symmetry, moment identities) hold for every Gaussian state; same instances
--   - encoding: probabilities as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals, measures); reason: every quantity is a nonnegative integral or a probability; same values
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Theorem 8.3, p.48 (PDF p.51), eq. (25); Siegel disk §4.4, pp.18–19 (PDF pp.21–22)

import Mathlib
import Definitions.Def_LogLogJam_Supplement_IsGaussQP
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_WildeQIT_Schumacher_tensorPow

open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

open LogLogJam

/-- **Theorem 8.3** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Theorem 8.3,
p.48, PDF p.51): "There is an absolute constant C > 0 such that for any n ≥ 1, 0 < ε ⩽ 1, and
0 < δ < 1, there is a POVM on m = C/ε² (n² + log(1/δ)) (25) copies of an unknown pure n-mode
Gaussian state ρ(0, V) whose outcome specifies a pure Gaussian state ρ(0, V̂) such that
Dtr(ρ(0, V), ρ(0, V̂)) ⩽ ε with probability at least 1 − δ."

There is an absolute `C > 0` such that for every `n ≥ 1`, `ε ∈ (0, 1]`, `δ ∈ (0, 1)` and every
number of copies `m ≥ C(n² + log(1/δ))/ε²` there is a POVM `M` on `m` copies of the `n`-mode Fock
space, with outcomes in the density operators, such that for every pure centered `n`-mode Gaussian
state `ρ`, measuring `ρ^{⊗m}` yields, with probability at least `1 − δ`, an outcome `σ` that is
a pure centered Gaussian state with `D_tr(σ, ρ) ≤ ε`.

**Formalization Note** Arbitrary (entangled, non-Gaussian) POVMs: the published
`BosonicLearn.FockPOVM` on the index type `Fin m → ℕⁿ` of `ℓ²(ℕⁿ)^{⊗m}`, with `ρ^{⊗m}` the published
`WildeQIT.Schumacher.tensorPow`; the POVM is chosen before the state. -/
theorem theorem_8_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
      ∀ m : ℕ, C / ε ^ 2 * ((n : ℝ) ^ 2 + Real.log (1 / δ)) ≤ m →
      ∃ M : BosonicLearn.FockPOVM (Fin m → Occupation (Fin n)) (State (Occupation (Fin n))),
        ∀ ρ : State (Occupation (Fin n)), IsPureCentGauss ρ →
          ENNReal.ofReal (1 - δ) ≤
            M.law (WildeQIT.Schumacher.tensorPow m ρ.coefficients)
              {σ | IsPureCentGauss σ ∧
                BosonicLearn.traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε} := by sorry

end LogLogJam.Supplement
