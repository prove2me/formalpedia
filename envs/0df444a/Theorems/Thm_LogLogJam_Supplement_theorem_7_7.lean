-- Prove2me | Theorems.Thm_LogLogJam_Supplement_theorem_7_7
-- name    : LogLogJam.Supplement.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:53:34.856377+00:00
-- url     : https://prove2.me/theorems/54267073-6a6e-4f01-8fd6-26eea6089606
-- title:
--   Theorem 7.7 — a $T$-round single-copy Gaussian protocol learns single-mode Gaussian states with $\tilde O(T\varepsilon^{-2^T/(2^T-1)}E^{1/(2^T-1)}+\varepsilon^{-2})$ copies
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every $T\ge2$, every energy bound $E\ge2$ and all $\varepsilon,\delta\in(0,1)$. There is a protocol with exactly $T$ rounds of adaptivity, each round one (possibly randomized) Gaussian measurement that measures every copy separately, that uses at most
--
--   $$
--   N\le C\Big(T\,\varepsilon^{-2^T/(2^T-1)}E^{1/(2^T-1)}+\varepsilon^{-2}\Big)\log\frac T\delta\cdot\log E\cdot\log\frac{E}{\varepsilon\delta}
--   $$
--
--   copies and, for every single-mode Gaussian state $\rho=\rho(m,V)$ (possibly mixed and displaced, $V\in\mathrm{Cov}_1$) of energy $\tfrac14\operatorname{tr}V+\tfrac12\|m\|_2^2\le E$, outputs an estimate $\hat\rho$ with
--
--   $$
--   \Pr\big[D_{\mathrm{tr}}(\hat\rho,\rho)\le\varepsilon\big]\ge1-\delta .
--   $$
--
--   For constant $T$ this matches the lower bound of Theorem 6.2 up to logarithmic factors, so bounded adaptivity already reduces the energy dependence from $E$ (nonadaptive) to $E^{1/(2^T-1)}$.
--
--   Differences from the source:
--
--   - reading: $O\big((T\varepsilon^{-2^T/(2^T-1)}E^{1/(2^T-1)}+\varepsilon^{-2})\log(T/\delta)\log E\log(E/\varepsilon\delta)\big)$ → an absolute constant $C>0$ chosen before $T,E,\varepsilon,\delta$, and a protocol using at most $N\le C(\dots)$ copies; reason: the standard meaning of $O$ for an existence claim with explicit parameters
--   - reading: $E$, $\varepsilon$, $\delta$ unrestricted in the statement → $E\ge2$ and $\varepsilon,\delta\in(0,1)$; reason: for $E\le1$, $\log E\le0$ and the bound is meaningless; any fixed $E_0>1$ is equivalent up to $C$. $\varepsilon,\delta\in(0,1)$ are the ranges of Lemma 7.6 and of the analysis; for $\varepsilon\ge1$ or $\delta\ge1$ the claim is void and $\log(E/\varepsilon\delta)$ may be nonpositive. Algorithm 1 asks $\varepsilon\le0.01$; larger $\varepsilon<1$ is covered by running it at $0.01$, which changes the bound by a constant factor
--   - encoding: an algorithm using single-copy Gaussian measurements with $T$ rounds of adaptivity → `SCGaussProtocol T`: exactly $T$ rounds, each one Gaussian measurement whose seed is a direct sum of single-copy seeds in $\mathrm{Cov}_1$, chosen by a Markov kernel from the history (randomized choices allowed, the number of copies $k$ may itself be random given the history, $k=0$ allowed); the output is a Markov kernel to density operators; reason: Definition 4.4: exactly $T$ rounds, an early stop is padded with null measurements, and randomness can be absorbed into the maps; single-copy measurements are direct sums of single-copy seeds (§4.2, p.17); same class
--   - encoding: sample complexity: the maximum number of copies over consistent length-$T$ histories → `SCCopiesLe P N`: at every round, from every history that has used at most $N$ copies, almost every drawn seed keeps the total at most $N$; reason: a consistent history is one the protocol can produce; same requirement up to null sets of seed draws, which change no probability
--   - encoding: a Gaussian measurement with seed $W$ applied to $k$ copies of $\rho(m,V)$ → its classical outcome law, the Gaussian density of $N(m\otimes 1_k,(V\otimes I_k+W)/2)$ on $\mathbb R^{2k}$; reason: §4.2 (p.17) defines a Gaussian measurement by this outcome law on Gaussian states, and every measurement in the statement is applied to copies of a Gaussian state; same instances
--   - encoding: the Gaussian state $\rho(m,V)$ with $V_{ij}=\mathrm{Tr}(\rho\{\hat R_i-m_i,\hat R_j-m_j\})$ (vacuum $V=I$), quadratures $(q_1,\dots,q_n,p_1,\dots,p_n)$ → a density operator on $\ell^2(\mathbb N^n)$ satisfying the published `BosonicLearn.IsGaussianState` with mean $m$ and covariance $V/2$, indices reindexed from $\mathrm{Fin}\,2\times\mathrm{Fin}\,n$ to $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$; reason: `IsGaussianState` uses $\Sigma=\tfrac12\mathrm{Tr}(\rho\{\cdot,\cdot\})$ (vacuum $\tfrac12 I$) with the same $\hat q,\hat p$ and grouped order; its extra clauses (finite energy, symmetry, moment identities) hold for every Gaussian state; same instances
--   - encoding: probabilities as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals, measures); reason: every quantity is a nonnegative integral or a probability; same values
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Theorem 7.7, pp.35–36 (PDF pp.38–39); setting of §7, p.34 (PDF p.37); Algorithm 1, p.36 (PDF p.39)

import Mathlib
import Definitions.Def_LogLogJam_Supplement_SCGaussProtocol

open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

open LogLogJam

/-- **Theorem 7.7** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Theorem 7.7,
pp.35–36, PDF pp.38–39): "For T ≥ 2, there exists an algorithm using single-copy Gaussian
measurements with T rounds of adaptivity that learns any single-mode Gaussian state ρ(m, V) to
trace distance ε with probability at least 1 − δ, promised that the energy of ρ is at most E. The
sample complexity is O((Tε^{−2^T/(2^T−1)}E^{1/(2^T−1)} + ε^{−2}) log(T/δ) · log(E) · log(E/εδ))."

There is an absolute `C > 0` such that for every `T ≥ 2`, `E ≥ 2`, `ε, δ ∈ (0, 1)` some `T`-round
protocol with (randomized) single-copy Gaussian measurements uses at most
`N ≤ C (Tε^{−2^T/(2^T−1)}E^{1/(2^T−1)} + ε^{−2}) log(T/δ) log E log(E/(εδ))` copies and, on every
single-mode Gaussian state `ρ = ρ(m, V)` (`V ∈ Cov_1`, possibly mixed and displaced) of energy
`¼ tr V + ½‖m‖² ≤ E`, outputs `ρ̂` with `D_tr(ρ̂, ρ) ≤ ε` with probability at least `1 − δ`.

**Formalization Note** `O(·)` read as an absolute constant chosen before `T, E, ε, δ`; `E ≥ 2`
keeps `log E` positive. A Gaussian measurement is its classical outcome law on `ρ(m, V)`
(§4.2, p.17); the quantum state `ρ` enters through `IsGaussQP` and the trace distance. -/
theorem theorem_7_7 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℕ), 2 ≤ T → ∀ E ε δ : ℝ, 2 ≤ E → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∃ (P : SCGaussProtocol T) (N : ℕ),
        (N : ℝ) ≤ C * (((T : ℝ) * ε ^ (-((2 : ℝ) ^ T / ((2 : ℝ) ^ T - 1))) *
              E ^ (1 / ((2 : ℝ) ^ T - 1)) + ε ^ (-(2 : ℝ))) *
            Real.log (T / δ) * Real.log E * Real.log (E / (ε * δ))) ∧
        SCCopiesLe P N ∧
        ∀ (m : Q 1 → ℝ) (V : Matrix (Q 1) (Q 1) ℝ), IsCov 1 V → energyGen m V ≤ E →
          ∀ ρ : State (Occupation (Fin 1)), IsGaussQP ρ m V →
            ENNReal.ofReal (1 - δ) ≤ scSuccProb m V ρ ε P := by sorry

end LogLogJam.Supplement
