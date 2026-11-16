-- Prove2me | Theorems.Thm_LogLogJam_Supplement_theorem_6_2
-- name    : LogLogJam.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:52:18.521356+00:00
-- url     : https://prove2.me/theorems/cbed8783-09dc-411a-a7c9-eee407d1e5d6
-- title:
--   Theorem 6.2 — $T$-adaptive Gaussian protocols: the success bound (17) and $S=\Omega(T^{-1}\varepsilon^{-2^T/(2^T-1)}E^{1/(2^T-1)})$
-- statement:
--   Fix $\lambda>1$ with energy $E=\tfrac14(\lambda+\lambda^{-1})>1$, an accuracy $\varepsilon\in(0,1/2)$ and a number of rounds $T\ge1$. Consider Task 5.1: $\theta$ is uniform on $\mathbb T=\mathbb R/\pi\mathbb Z$, the learner gets copies of the squeezed vacuum $\rho_{\lambda,\theta}$ and must output $\hat\theta$ with $D_{\mathrm{tr}}(\rho_{\hat\theta},\rho_\theta)\le\varepsilon$.
--
--   1. Every $T$-adaptive protocol with (randomized, possibly entangled) Gaussian measurements that uses at most $S$ copies succeeds with probability
--
--   $$
--   p_{\mathrm{succ}}\le\frac{2\varepsilon}{E}+16\pi^2\varepsilon\,(T+1)\,(1+S)^{1-2^{-T}}\,(8\pi E)^{-2^{-T}} .\qquad(17)
--   $$
--
--   2. Consequently there are constants $c>0$ and $E_0>1$ such that, whenever $E\ge E_0$, every such protocol with $p_{\mathrm{succ}}\ge2/3$ uses
--
--   $$
--   S\ \ge\ c\,T^{-1}\,\varepsilon^{-2^T/(2^T-1)}\,E^{1/(2^T-1)}
--   $$
--
--   copies.
--
--   This interpolates between the nonadaptive bound $\Omega(E/\varepsilon^2)$ at $T=1$ (Corollary 6.3) and the $\Omega(\log\log E)$ bound for fully adaptive protocols (Theorem 6.5), and is matched up to logarithmic factors by Theorem 7.7.
--
--   Differences from the source:
--
--   - reading: the success probability of $\mathcal P$ in solving Gaussian state tomography (Task 4.2) with energy parameter $E$ and accuracy $\varepsilon$ → the success probability on Task 5.1: $\theta$ uniform on $\mathbb T$, the protocol runs on the squeezed vacuum $\rho_{\lambda,\theta}$ of energy $E$ and outputs $\hat\theta$, success when $D_{\mathrm{tr}}(\rho_{\hat\theta},\rho_\theta)\le\varepsilon$; reason: Task 4.2 asks for success on every state and defines no single success probability; the proof says 'By the reduction in Lemma 5.2, it suffices to prove the bound for Task 5.1' and proves (17) for Task 5.1, as the published `LogLogJam.theorem_6_5` and `eq_14` do. A Task 4.2 protocol at accuracy $\varepsilon$ is a Task 5.1 protocol at $2\varepsilon$ with the same copies (Lemma 5.2); the factor 2 is absorbed by $\Omega$ in the second clause
--   - reading: $\Omega(T^{-1}\varepsilon^{-2^T/(2^T-1)}E^{1/(2^T-1)})$ → constants $c>0$ and $E_0>1$ chosen before $\lambda,\varepsilon,T$, the protocol and $S$, with $S\ge c\,T^{-1}\varepsilon^{-2^T/(2^T-1)}E^{1/(2^T-1)}$ for all $E\ge E_0$ and $\varepsilon\in(0,1/2)$; reason: the standard meaning of $\Omega$ uniform in $T$ and $\varepsilon$; $E\ge E_0$ is needed since the $2\varepsilon/E$ term of (17) alone can exceed $2/3$ for $E$ close to $1$
--   - reading: $\varepsilon<1/2$ → $0<\varepsilon<1/2$; reason: $\varepsilon$ is an accuracy parameter, positive by Task 4.2; $\varepsilon^{-2^T/(2^T-1)}$ is undefined at $\varepsilon\le0$
--   - reading: a $T$-adaptive protocol → $T\ge1$; reason: Definition 4.4: $T=1$ is the nonadaptive case; the exponents $2^T/(2^T-1)$ and $1/(2^T-1)$ are undefined at $T=0$
--   - generalization: Definition 4.4: the measurement map gives, at each history, a randomized Gaussian measurement on a number $k$ of copies fixed by the history → a Markov kernel from histories to pairs $(k,W)$ (the published `LogLogJam.GaussProtocol`), so $k$ may also be random given the history; the drawn seed is recorded in the observation; reason: Definition 4.4's protocols are the kernels whose $k$-marginal is a Dirac mass; continuous ensembles are allowed by p.17
--   - generalization: sample complexity $S$: the maximum number of copies over consistent length-$T$ histories → `CopiesLe`: for every $\theta$, almost every length-$T$ history uses at most $S$ copies; reason: a weaker hypothesis: a bound on every consistent history implies the almost-sure bound
--   - encoding: the protocol's maps (no regularity stated) → the seed kernels and the output map are measurable, and seeds lie in $\mathrm{Cov}_k$ almost surely; reason: without measurability the success probability is undefined; this excludes only undefined cases
--   - encoding: a Gaussian measurement with seed $W\in\mathrm{Cov}_k$ applied to $\rho_\theta^{\otimes k}$ → its classical outcome law, the density $\exp(-y^\top D^{-1}y)/(\pi^k\sqrt{\det D})$ with $D=V_\theta\otimes I_k+W$; reason: §4.2 (p.17) defines a Gaussian measurement by this outcome law on Gaussian states; same instances
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects, uniform law on $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic; same instances
--   - encoding: the trace distance of two squeezed vacua → $\sqrt{1-2/\sqrt{\det(V_{\lambda,\theta}+V_{\lambda,\theta'})}}$; reason: Lemma 4.1 (pp.15–16) for pure zero-mean single-mode Gaussian states; same values
--   - encoding: energy $E>1$ and $\lambda>1$ the solution of $E=\tfrac14(\lambda+\lambda^{-1})$ → $\lambda>1$ as the parameter with $E=\mathrm{energy}\,\lambda$ and $1<E$; reason: $\lambda\mapsto(\lambda+\lambda^{-1})/4$ is a bijection from $(1,\infty)$ onto $(1/2,\infty)$; same instances
--   - encoding: probabilities as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals, measures); reason: every quantity is a nonnegative integral or a probability; same values
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Theorem 6.2, p.32 (PDF p.35), eq. (17); proof via Lemma 5.2, p.22 (PDF p.25), eqs. (14), (16)

import Mathlib
import Definitions.Def_LogLogJam_GaussProtocol

open scoped ENNReal

namespace LogLogJam.Supplement

open LogLogJam

/-- **Theorem 6.2** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Theorem 6.2,
p.32, PDF p.35): "Let E > 1, ε < 1/2. Suppose P is a T-adaptive Gaussian learning protocol with
sample complexity S. Then the success probability of P in solving Gaussian state tomography with
energy parameter E and accuracy parameter ε is at most
p_succ ≤ 2ε/E + 16π²ε(T + 1)(1 + S)^{1−2^{−T}}(8πE)^{−2^{−T}}. (17)
In conclusion, to achieve a 2/3 success probability, the sample complexity is at least
Ω(T^{−1}ε^{−2^T/(2^T−1)}E^{1/(2^T−1)})."

Both clauses, for Task 5.1 (the proof: "By the reduction in Lemma 5.2, it suffices to prove the
bound for Task 5.1"):
1. the bound (17) with its printed constants, for every `T ≥ 1`, `λ > 1` with `E = energy lam > 1`,
   `ε ∈ (0, 1/2)` and every protocol using at most `S` copies;
2. constants `c > 0`, `E₀ > 1` fixed first such that every protocol with success probability at least
   `2/3` at energy `E ≥ E₀` uses `S ≥ c T⁻¹ ε^{−2^T/(2^T−1)} E^{1/(2^T−1)}` copies.

**Formalization Note** Task 5.1 in place of Task 4.2 (Lemma 5.2, `ε ↦ 2ε`, absorbed by `Ω` in
clause 2), as in the published `LogLogJam.theorem_6_5`; `T ≥ 1` (Definition 4.4, `T = 1` is
nonadaptive); real powers `x ^ (r : ℝ)` with positive bases. -/
theorem theorem_6_2 :
    (∀ (T : ℕ), 1 ≤ T → ∀ lam : ℝ, 1 < lam → 1 < energy lam →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ (P : GaussProtocol T) (S : ℕ), CopiesLe lam P S →
        succProb lam ε P ≤ ENNReal.ofReal (2 * ε / energy lam +
          16 * Real.pi ^ 2 * ε * ((T : ℝ) + 1) * (1 + (S : ℝ)) ^ (1 - (2 : ℝ) ^ (-(T : ℝ))) *
            (8 * Real.pi * energy lam) ^ (-((2 : ℝ) ^ (-(T : ℝ)))))) ∧
    (∃ c E₀ : ℝ, 0 < c ∧ 1 < E₀ ∧
      ∀ lam : ℝ, 1 < lam → E₀ ≤ energy lam →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ (T : ℕ), 1 ≤ T → ∀ (P : GaussProtocol T) (S : ℕ),
        CopiesLe lam P S → (2 / 3 : ℝ≥0∞) ≤ succProb lam ε P →
        c * ((T : ℝ)⁻¹ * ε ^ (-((2 : ℝ) ^ T / ((2 : ℝ) ^ T - 1))) *
          energy lam ^ (1 / ((2 : ℝ) ^ T - 1))) ≤ S) := by sorry

end LogLogJam.Supplement
