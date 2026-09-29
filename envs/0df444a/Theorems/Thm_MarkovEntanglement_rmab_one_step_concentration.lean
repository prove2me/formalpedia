-- Prove2me | Theorems.Thm_MarkovEntanglement_rmab_one_step_concentration
-- name    : MarkovEntanglement.rmab_one_step_concentration
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-28T02:23:18.304042+00:00
-- url     : https://prove2.me/theorems/24993da8-6a3b-4aa7-9340-0968a06678bf
-- title:
--   One-step concentration of the configuration (Lem. 9, Gast et al. 2024)
-- statement:
--   Consider one step of the $N$-agent restless-bandit chain under an index policy, started from an arbitrary joint state $s$, and let $\varphi$ be the explicit mean-field map of the configuration, taken at the exact activation fraction $\lfloor \alpha N \rfloor / N$ of the $N$-agent system. Writing $\epsilon[1] = m[1] - \varphi(m[0])$ for the one-step deviation of the configuration from its mean-field image,
--
--   $$\mathbb{E}\big[\|\epsilon[1]\|_1 \;\big|\; m[0]\big] \;\le\; \sqrt{\frac{|S|}{N}}.$$
--
--   The mechanism is the usual $1/\sqrt{N}$ of an average of $N$ indicators. Conditionally on the current joint state, the index policy activates a deterministic number of agents in each local state — only *which* agents is random, and the agents in a state are exchangeable — so the next local states are an independent family: for each local state $x$, a fixed number of draws from $P_1(x, \cdot)$ and a fixed number from $P_0(x,\cdot)$. The next configuration is their average, its mean is exactly $\varphi(m[0])$ by definition of the mean-field map, and each coordinate has variance at most $1/N$ times its mean. Bounding each $\mathbb{E}|\epsilon_x|$ by the standard deviation and then summing over $x$ with Cauchy–Schwarz produces $\sqrt{|S|/N}$.
--
--   This is the input that fixes the rate in Theorem 7: everything downstream amplifies it by constants that do not depend on $N$.
-- source:
--   Nicolas Gast, Bruno Gaujal and Chen Yan, 'Reoptimization nearly solves weakly coupled Markov decision processes' (2024), Lemma 1; cited as Lemma 9 in Chen and Peng, arXiv:2506.02385v3, Appendix I, p. 43

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Lemma 9 (One-step Concentration; Lemma 1 of Gast, Gaujal and Yan 2024).  Starting from any
joint state, the configuration after one step deviates from its mean-field image by at most
`√(|S| / N)` in expected `ℓ¹` norm:

`E[‖m[1] − φ(m[0])‖₁ ∣ m[0]] ≤ √(|S| / N)`.

The expectation is over one step of the `N`-agent chain, the mean-field map is the explicit
one at the exact activation fraction `⌊αN⌋ / N` of the `N`-agent system, and the rate is the
usual `1/√N` of an average of `N` conditionally independent indicators. -/
theorem rmab_one_step_concentration
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (α : ℝ) (N : ℕ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π)
    (s : Fin N → S) :
    ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
        l1Norm (fun x => configuration s' x
          - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)) (configuration s) x)
      ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
  sorry

/-! ### M5 — Lemma 10, multi-step concentration (Gast, Gaujal and Yan) -/

end MarkovEntanglement
