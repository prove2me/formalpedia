-- Prove2me | Theorems.Thm_MultiNashRepair_theorem_1_1
-- name    : MultiNashRepair.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:30:45.239193+00:00
-- url     : https://prove2.me/theorems/21cfa844-f170-42d9-bbb3-1e4b358ac043
-- title:
--   Theorem 1.1 — polynomial-time $(1-\sigma/m)$-approximate Nash equilibria of $m$-player games for every rational $\sigma\in(1,\sigma_\star)$
-- statement:
--   Let $\sigma_\star\approx1.5867$ be the unique root in $(1,2)$ of
--   $$\sigma^3-19\sigma^2+27\sigma+1=0 .$$
--   There is a computable threshold $m_0(\sigma)$ such that, for every fixed rational $\sigma\in(1,\sigma_\star)$, there are one multi-stack Turing machine $M_\sigma$ and one constant $c_\sigma$ with the following property. For every $m\ge m_0(\sigma)$ and every $m$-player game with nonempty finite action sets and rational payoffs in $[0,1]$, given as a complete payoff table whose binary encoding has length $N$, the machine outputs within $c_\sigma(N+2)^{c_\sigma}$ steps a rational mixed profile $x$ with
--   $$\mathrm{Reg}(x)\le1-\frac{\sigma}{m},$$
--   i.e. a rational $(1-\sigma/m)$-approximate Nash equilibrium.
--
--   Repeated one-player extension only reaches $1-1/m$ (and $1-1/(m-c)$ from any improved fixed-player base case); this theorem improves the leading coefficient of $1/m$ from $1$ to any fixed value below $\sigma_\star$.
--
--   **Formalization Note** A positive rational $\sigma$ is written $(a+1)/(b+1)$ and the threshold is a computable function of $(a,b)$.
--
--   Differences from the source:
--   - reading: computed in polynomial time (no machine model named) → one multi-stack Turing machine and one exponent $c$ with time at most $c(N+2)^c$ on inputs of length $N$ (the published `CFLOutliers.OutputsWithin`), outputting the encoding of the profile; reason: the paper names no model; polynomial time is invariant under polynomial simulations
--   - reading: computable threshold $m_0(\sigma)$ for rational $\sigma$ → `Computable₂ m0` on $(a,b)$ with $\sigma=(a+1)/(b+1)$; reason: Mathlib has no `Primcodable ℚ`; every positive rational has this form
--   - encoding: $\sigma_\star$ the unique root in $(1,2)$ of $\sigma^3-19\sigma^2+27\sigma+1$ → `sigmaStar`, the supremum of $\{s\in[1,2]: p(s)\ge0\}$; reason: $p$ is strictly decreasing on $[1,2]$ with $p(1)>0>p(2)$, so the supremum is the root (Theorem 5.8 milestone)
--   - encoding: $x$ is an $\varepsilon$-approximate Nash equilibrium, $\mathrm{Reg}(x)\le\varepsilon$ (pure deviations) → `IsEpsApproxNash` (every mixed unilateral deviation gains at most $\varepsilon$); reason: by multilinearity the best mixed deviation gains at most the best pure deviation; equivalent
--   - encoding: players $[m]$, nonempty action sets $A_i$, payoffs in $[0,1]\cap\mathbb Q$, the binary input → the published `Table m` (players `Fin m`, actions `Fin (n i)`, payoffs $p/q$ with $p\le q$, possibly unreduced) and its encoding `encGame`; reason: Lean representation of the paper's input; the same instances
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_MultiNashRepair_ScalarCertificate

open OnlineCRS.Combine (Sym)
open NashAmplification.Filtering (Table RawProfile encGame encProfile)

namespace MultiNashRepair

/-- **Theorem 1.1 (Approximate Nash Equilibria in Multiplayer Games)** (Tang, Ding, Fang,
arXiv:2611.06076, Theorem 1.1, p.3).

Let `σ⋆` be the unique root in `(1, 2)` of `σ³ − 19σ² + 27σ + 1`. There is a computable threshold
`m0`, and for every rational `σ ∈ (1, σ⋆)` one machine `M` and one exponent `c`, such that for
every `m ≥ m0(σ)` and every complete rational `m`-player table `G` with payoffs in `[0,1]`, `M`
outputs on `encGame G`, within `c (|encGame G| + 2)^c` steps, the encoding of a rational profile
that is a `(1 − σ/m)`-approximate Nash equilibrium of `G`.

**Formalization Note.**
- Rational `σ > 0` is written `σ = (a+1)/(b+1)` with `a, b : ℕ`, and the threshold is a
  `Computable₂` function of `(a, b)`: Mathlib has no `Primcodable ℚ`.
- "Computes … in time polynomial in the input bit length" is one `TM2` machine over the published
  alphabet `Sym` per `σ`, uniform in `m` and `G`, with time `c (N + 2)^c` in the input length `N`;
  the exponent may depend on `σ` (`B^{O_σ(1)}`, Proposition 4.6).
- Games are `NashAmplification.Filtering.Table m` (players `Fin m`, nonempty action sets
  `Fin (n i)`, payoffs `num/den ≤ 1`, possibly unreduced). `IsEpsApproxNash` uses mixed
  deviations; it is equivalent to the paper's `Reg(x) ≤ ε` by multilinearity.
- `σ⋆` is `sigmaStar`, the supremum of `{s ∈ [1,2] | p(s) ≥ 0}`, which is the unique root
  (Theorem 5.8 milestone). The threshold `1 − σ/m` is real division with `m` cast to `ℝ`. -/
theorem theorem_1_1 :
    ∃ m0 : ℕ → ℕ → ℕ, Computable₂ m0 ∧
      ∀ a b : ℕ, let σ : ℚ := (a + 1) / (b + 1)
        1 < σ → (σ : ℝ) < sigmaStar →
        ∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ),
          ∀ m : ℕ, m0 a b ≤ m → ∀ G : Table m,
            ∃ x : RawProfile m, x.sizes = G.sizes ∧
              CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
              DGPNash.WellSupported.IsEpsApproxNash G.utility (x.on G.counts)
                (1 - (σ : ℝ) / m) := by sorry

end MultiNashRepair
