-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_example_1_1
-- name    : LogSobolevMC.Metropolis.example_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:19.867299+00:00
-- url     : https://prove2.me/theorems/caa40b27-3e3d-4637-b82b-49cbb510558c
-- title:
--   Example 1.1, (1.9), p. 698 — the Metropolis chain for the binomial distribution is the kernel (1.9) and is reversible
-- statement:
--   Let $n\ge 1$, $\mathcal X=\{0,\dots,n\}$, $\pi(x)=2^{-n}\binom nx$, and let $M$ be the Metropolis chain built from the nearest-neighbour walk $K$ (with holding $1/2$ at $0$ and $n$) and $\pi$: $M(x,y)=K(x,y)\min\{1,\pi(y)/\pi(x)\}$ for $y\ne x$ and $M(x,x)=1-\sum_{y\ne x}M(x,y)$. Then $M$ is a Markov kernel, it is given by
--
--   $$M(x,y)=\begin{cases}\tfrac12, & y=x+1,\ 0\le x\le \tfrac{n-1}2,\ \text{or } y=x-1,\ \tfrac{n+1}2\le x\le n,\\[2pt] \dfrac{x}{2(n-x+1)}, & y=x-1,\ 1\le x\le\tfrac{n+1}2,\\[2pt] \dfrac{n-x}{2(x+1)}, & y=x+1,\ \tfrac{n-1}2\le x\le n-1,\\[2pt] \dfrac{n-2x+1}{2(n-x+1)}, & y=x,\ 0\le x\le\tfrac{n-1}2,\\[2pt] \dfrac{2x-n+1}{2(x+1)}, & y=x,\ \tfrac{n+1}2\le x\le n,\\[2pt] \dfrac{2}{n+2}, & y=x=\tfrac n2\ (n\text{ even}),\end{cases}$$
--
--   and $M(x,y)=0$ when $|x-y|\ge 2$; moreover $\pi(x)M(x,y)=\pi(y)M(y,x)$ for all $x,y$.
--
--   This identifies the abstract Metropolis construction with the explicit chain (1.9) studied in the paper, and records the reversibility that makes $\pi$ stationary.
--
--   **Formalization Note** Each case of the display is a separate implication; the bounds such as $x\le (n-1)/2$ are compared in $\mathbb R$. The "$0$ otherwise" clause, implicit on the page, is stated for $y\notin\{x-1,x,x+1\}$.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 698, Example 1.1, (1.9)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Example 1.1, (1.9), p. 698: the standard Metropolis construction on the nearest-neighbour
walk gives the six-case kernel (1.9) (and `M(x, y) = 0` for `|x − y| ≥ 2`), and
`π(x)M(x, y) = π(y)M(y, x)` for the binomial distribution `π`. -/
theorem example_1_1 (n : ℕ) (hn : 1 ≤ n) :
    MarkovMixing.IsStochastic (binomMetropolis n) ∧
    (∀ x y : Fin (n + 1),
      (((y : ℕ) = (x : ℕ) + 1 ∧ 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1) ∨
        ((y : ℕ) + 1 = (x : ℕ) ∧ (n : ℝ) + 1 ≤ 2 * ((x : ℕ) : ℝ))) →
      binomMetropolis n x y = 1 / 2) ∧
    (∀ x y : Fin (n + 1),
      (y : ℕ) + 1 = (x : ℕ) → 1 ≤ ((x : ℕ) : ℝ) → 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) + 1 →
      binomMetropolis n x y = ((x : ℕ) : ℝ) / (2 * ((n : ℝ) - ((x : ℕ) : ℝ) + 1))) ∧
    (∀ x y : Fin (n + 1),
      (y : ℕ) = (x : ℕ) + 1 → (n : ℝ) - 1 ≤ 2 * ((x : ℕ) : ℝ) → ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1 →
      binomMetropolis n x y = ((n : ℝ) - ((x : ℕ) : ℝ)) / (2 * (((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), 2 * ((x : ℕ) : ℝ) ≤ (n : ℝ) - 1 →
      binomMetropolis n x x =
        ((n : ℝ) - 2 * ((x : ℕ) : ℝ) + 1) / (2 * ((n : ℝ) - ((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), (n : ℝ) + 1 ≤ 2 * ((x : ℕ) : ℝ) →
      binomMetropolis n x x =
        (2 * ((x : ℕ) : ℝ) - (n : ℝ) + 1) / (2 * (((x : ℕ) : ℝ) + 1))) ∧
    (∀ x : Fin (n + 1), 2 * (x : ℕ) = n →
      binomMetropolis n x x = 2 / ((n : ℝ) + 2)) ∧
    (∀ x y : Fin (n + 1), x ≠ y → (y : ℕ) ≠ (x : ℕ) + 1 → (y : ℕ) + 1 ≠ (x : ℕ) →
      binomMetropolis n x y = 0) ∧
    MarkovMixing.DetailedBalance (binomMetropolis n) (binomPi n) := by sorry

end LogSobolevMC.Metropolis
