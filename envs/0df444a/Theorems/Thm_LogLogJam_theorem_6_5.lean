-- Prove2me | Theorems.Thm_LogLogJam_theorem_6_5
-- name    : LogLogJam.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:35.146386+00:00
-- url     : https://prove2.me/theorems/f36a1b5d-9006-4187-a2f1-d1d73d2b4065
-- title:
--   Theorem 6.5 — adaptive Gaussian protocols need $\Omega(\log\log E)$ copies
-- statement:
--   There are constants $c>0$ and $E_0>1$ such that the following holds. Let $\lambda>1$ with energy $E=\tfrac14(\lambda+\lambda^{-1})\ge E_0$ and let $\varepsilon\in(0,1/2)$. Every $T$-adaptive protocol with (randomized, possibly entangled) Gaussian measurements that uses at most $S$ copies and solves Task 5.1 with success probability at least $2/3$ satisfies
--
--   $$
--   S\ge c\,\log\log E .
--   $$
--
--   This is the energy half of Theorem 1.1: the $\log\log E$ term of the best known protocol cannot be removed with Gaussian measurements.
--
--   Differences from the source:
--
--   - generalization: Task 4.2: output a description of any state, succeed with probability $\ge 2/3$ on every state of energy at most $E$ → Task 5.1: $\theta$ uniform on $\mathbb T$, output $\hat\theta$, succeed when $D_{\mathrm{tr}}(\rho_{\hat\theta},\rho_\theta)\le\varepsilon$ with probability $\ge2/3$; reason: Lemma 5.2 (p.22) turns a Task 4.2 protocol at accuracy $\varepsilon$ into a Task 5.1 protocol at $2\varepsilon$ with the same copies; the factor 2 is absorbed by $\Omega$, so the Lean bound implies the source's (the paper proves Theorems 6.2 and 6.5 this way)
--   - reading: $\Omega(\cdot)$ → constants $c>0$, $E_0>1$ (and $\varepsilon_0$) chosen before $\lambda,\varepsilon,T$, the protocol and $S$, with the bound for all $E\ge E_0$; reason: the standard two-parameter meaning of $\Omega$; $\log\log E$ is negative for $E<e$ and Theorem 6.5 assumes $E>1$
--   - reading: “$\varepsilon<1/2$” → $0<\varepsilon<1/2$; reason: $\varepsilon$ is an accuracy parameter, positive by Task 4.2
--   - generalization: Definition 4.4: the measurement map gives, at each history, a randomized Gaussian measurement on a number $k$ of copies fixed by the history → a Markov kernel from histories to pairs $(k,W)$, so $k$ may also be random given the history; the drawn seed is recorded in the observation; reason: Definition 4.4's protocols are the kernels whose $k$-marginal is a Dirac mass; continuous ensembles are allowed by p.17
--   - generalization: sample complexity: the maximum number of copies over consistent length-$T$ histories → `CopiesLe`: for every $\theta$, almost every length-$T$ history uses at most $S$ copies; reason: a weaker hypothesis: a bound on every consistent history implies the almost-sure bound
--   - encoding: the protocol's maps (no regularity stated) → the seed kernels and the output map are measurable, and seeds lie in $\mathrm{Cov}_k$ almost surely; reason: without measurability the success probability is undefined; this excludes only undefined cases
--   - encoding: a Gaussian measurement with seed $W\in\mathrm{Cov}_k$ applied to the quantum state $\rho_\theta^{\otimes k}$ → its classical outcome law, the density $f^W_\theta(y)=\exp(-y^\top D^{-1}y)/(\pi^k\sqrt{\det D})$ with $D=V_\theta\otimes I_k+W$; reason: §4.2 (p.17) defines a Gaussian measurement by this outcome law on Gaussian states, and every measurement in the statement is applied to copies of $\rho_\theta$; same instances
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law and integrals on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects; uniform law and integrals over $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic, so $[0,\pi)$ is one period; same instances
--   - encoding: the trace distance $D_{\mathrm{tr}}(\rho_{\theta'},\rho_\theta)$ of quantum states → $\sqrt{1-2/\sqrt{\det(V_{\lambda,\theta}+V_{\lambda,\theta'})}}$; reason: Lemma 4.1 (pp.15–16) for pure zero-mean single-mode Gaussian states; same values
--   - encoding: energy $E>1/2$ and $\lambda>1$ the solution of $E=\tfrac14(\lambda+\lambda^{-1})$ → $\lambda>1$ as the parameter, $E=\mathrm{energy}\,\lambda=(\lambda+\lambda^{-1})/4$; reason: $\lambda\mapsto(\lambda+\lambda^{-1})/4$ is a bijection from $(1,\infty)$ onto $(1/2,\infty)$; same instances
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Theorem 6.5, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_LogLogJam_GaussProtocol

open scoped ENNReal

namespace LogLogJam

/-- **Theorem 6.5** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Theorem 6.5, p.33): "Let E > 1, ε < 1/2. The sample complexity for
Gaussian state tomography using adaptive Gaussian protocols is at least Ω(log log E)."

Stated for Task 5.1: there are `c > 0` and `E₀ > 1`, fixed first, such that for every `λ > 1` with
`E = energy lam ≥ E₀`, every `ε ∈ (0, 1/2)`, every `T` and every protocol using at most `S` copies
with success probability at least `2/3`, `c log log E ≤ S`.

**Formalization Note** Task 5.1 in place of Task 4.2 (Lemma 5.2, `ε ↦ 2ε`); `Ω` read with the
constants before `λ`, `ε`, `T`, the protocol and `S`; the bound is uniform in `ε ∈ (0, 1/2)`. -/
theorem theorem_6_5 :
    ∃ c E₀ : ℝ, 0 < c ∧ 1 < E₀ ∧
      ∀ lam : ℝ, 1 < lam → E₀ ≤ energy lam →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ (T : ℕ) (P : GaussProtocol T) (S : ℕ),
        CopiesLe lam P S → (2 / 3 : ℝ≥0∞) ≤ succProb lam ε P →
        c * Real.log (Real.log (energy lam)) ≤ S := by sorry

end LogLogJam
