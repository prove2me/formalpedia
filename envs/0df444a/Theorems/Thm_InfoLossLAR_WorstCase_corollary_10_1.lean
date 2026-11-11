-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_corollary_10_1
-- name    : InfoLossLAR.WorstCase.corollary_10_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:06:53.709823+00:00
-- url     : https://prove2.me/theorems/d3ccd963-6ab4-4a7e-9490-45b905a7246a
-- title:
--   Corollary 10.1 — a decisional LAR distinguisher for the fixed family yields quantum worst-case $\mathrm{GapSVP}_\gamma$ and $\mathrm{SIVP}_\gamma$ solvers, $\gamma=\tilde O(q)$
-- statement:
--   Consider the fixed public family of §9.9: $N=\lambda$, $\sigma=\lambda+2$, $q=q(\lambda)$ the least prime $\ge2^{16}(\lambda+2)^{64}$, $d=q(\lambda+2)^{96}+2(\lambda+2)^{128}$, the rounding matrix $T$ and quotient encoding $P=\mathbf 1^\top$ of Definition 6.3, so that the decisional LAR experiment draws $s\leftarrow U(\mathbb F_q^N)$, $M_i\leftarrow U(\mathbb F_q^{d\times N})$ and labels $f_T(M_is)=\sum_j\lfloor(T[M_is]_q)_j/q\rfloor\bmod q$.
--
--   There are constants $C,k\in\mathbb N$, fixed before the adversary, such that with
--   $$\gamma(\lambda)=C\cdot q(\lambda)\cdot(\log_2(\lambda+2))^k\qquad(\gamma=\tilde O(Nq/\sigma)=\tilde O(q)),$$
--   for every uniform QPT distinguisher $D$ on classical inputs, every positive polynomially bounded sample count $t$, every $c\in\mathbb N$ and every infinite set $S$ of security parameters with $\mathrm{Adv}^{\mathrm{dLAR}}_D(\lambda,t(\lambda))\ge\lambda^{-c}$ for all $\lambda\in S$, there are a uniform QPT algorithm that solves worst-case $\mathrm{GapSVP}_\gamma$ and a uniform QPT algorithm that solves worst-case $\mathrm{SIVP}_\gamma$ in dimension $N=\lambda$, for every $\lambda\in S$.
--
--   This is the paper's main reduction (Theorem 1.1): quantum worst-case hardness of $\mathrm{GapSVP}_{\tilde O(q)}$ or $\mathrm{SIVP}_{\tilde O(q)}$ on infinitely many dimensions implies decisional LAR hardness for every polynomial sample count.
--
--   Differences from the source:
--   - reading: "uniform QPT distinguisher", "uniform quantum polynomial-time algorithms" → `IsQPT`/`IsMQPT`: uniform Clifford+T circuit families (no advice, fixed gate set) on binary-coded classical inputs, Born-rule measurement of the output wires; reason: the paper names no model
--   - reading: "approximation factor $\tilde O(Nq/\sigma)=\tilde O(q)$" → $\exists C,k$ fixed before $D$, $\gamma=C\,q\,(\log_2(\lambda+2))^k$; reason: $\tilde O$ is a constant times a polylogarithmic factor; a larger $\gamma$ only makes both problems easier
--   - reading: "nonnegligible advantage" and "guaranteed only on infinitely many security parameters … succeed on those parameters" → for every $c$ and every infinite $S$ with advantage $\ge\lambda^{-c}$ on $S$, solvers succeeding at every $\lambda\in S$; reason: not negligible means $\ge\lambda^{-c}$ infinitely often; the algorithms do not depend on $\lambda$
--   - reading: worst-case GapSVP$_\gamma$/SIVP$_\gamma$ → nonsingular integer bases in binary, Euclidean norm, rational gap parameter $\delta>0$, success probability $\ge\frac23$ on every instance, SIVP output = code of $N$ integer lattice vectors at the start of the output string; reason: standard conventions of the cited [Reg05], not restated by the paper
--   - encoding: security parameters → $\lambda\ge1$ for $\lambda\in S$; reason: §3.1 indexes families by $\lambda\ge1$
--   - encoding: the third sentence (worst-case hardness implies dLAR hardness) → not a separate clause; reason: it is the contrapositive of the stated implication
--   - encoding: pp of the fixed family → the code of $(q,N,d,\sigma)$; reason: $T$ and $P$ are determined by $(q,d)$
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 60, Corollary 10.1 (with §9.9, p. 58, and Appendix I.1, pp. 132–133)

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

/-- Corollary 10.1 (Worst-case foundation for decisional LAR), p. 60, for the fixed family of
§9.9 (`N = λ`, `σ = λ + 2`, `q` the least prime `≥ 2^{16}(λ + 2)^{64}`,
`d = q(λ + 2)^{96} + 2(λ + 2)^{128}`, `T` and `P = 1ᵀ` of Definition 6.3). There are constants
`C, k ∈ ℕ`, fixed before the adversary, such that with `γ(λ) = C · q(λ) · (log₂(λ + 2))^k`
(`γ = Õ(Nq/σ) = Õ(q)`): for every uniform QPT distinguisher `D`, every positive polynomially
bounded sample count `t`, every `c` and every infinite set `S` of security parameters on which
`Adv^{dLAR}_D(λ, t(λ)) ≥ λ^{−c}`, there are a uniform QPT algorithm that solves worst-case
GapSVP_γ and a uniform QPT algorithm that solves worst-case SIVP_γ in dimension `N = λ`, for
every `λ ∈ S`. -/
theorem corollary_10_1 :
    ∃ C k : ℕ, ∀ D : Family, IsQPT D →
      ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
        ∀ c : ℕ, ∀ S : Set ℕ, S.Infinite → (∀ lam ∈ S, 1 ≤ lam) →
          (∀ lam ∈ S, (lam : ℝ) ^ (-(c : ℝ)) ≤ famAdvLAR D lam (t lam)) →
            (∃ A : Family, IsQPT A ∧ ∀ lam ∈ S,
              SolvesGapSVP A (famN lam)
                ((C : ℝ) * (famq lam : ℝ) * Real.logb 2 ((lam : ℝ) + 2) ^ k)) ∧
            (∃ A : MFamily, IsMQPT A ∧ ∀ lam ∈ S,
              SolvesSIVP A (famN lam)
                ((C : ℝ) * (famq lam : ℝ) * Real.logb 2 ((lam : ℝ) + 2) ^ k)) := by sorry

end InfoLossLAR.WorstCase
