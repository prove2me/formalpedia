-- Prove2me | Theorems.Thm_GevreyGibbsSep_eq_44
-- name    : GevreyGibbsSep.eq_44
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:46:04.757534+00:00
-- url     : https://prove2.me/theorems/939f52bc-7cd9-4c06-bd29-4e7fcc03ec0b
-- title:
--   Eq. (44) — $N_q\in\widetilde O(\alpha^{1/2+1/d}d^{5/2+s}(\log\alpha)^s(d+\log\alpha+\log\frac1\varepsilon)^s\log^2\frac1\varepsilon)$ at the separation parameters
-- statement:
--   Let $s>1$ and fix a window $0<c_0\le C_0$. Substituting $\xi=1/2$ and a radius with $c_0X\le1/\rho\le C_0X$, $X=d^{1+s}\alpha^{1/d}(\log\alpha)^s$, into (8) gives
--   $$N_q\in\widetilde O\Big(\alpha^{\frac12+\frac1d}d^{\frac52+s}(\log\alpha)^s\Big(d+\log\alpha+\log\frac1\varepsilon\Big)^s\log^2\frac1\varepsilon\Big):$$
--   there are $C>0$ and $m\in\mathbb N$ such that for every integer $d>2s$, every $\alpha\ge9$, every such $\rho$ and every $0<\varepsilon<1/2$, a first-order quantum algorithm chosen before the instance (taking $\beta$ as input) samples every member of $\mathscr W^s(\alpha,1/2,\rho)$ at accuracy $\varepsilon$ with at most $C\cdot F_{44}\cdot\log(\alpha d/\varepsilon)^m$ queries.
--
--   Differences from the source:
--   - generalization: the radius $\rho_{\alpha,d}$ of Theorem 4 → every radius in any window $c_0X\le1/\rho\le C_0X$, $0<c_0\le C_0$ (constants $C,m$ may depend on $c_0,C_0$); reason: Theorem 4's radius lies in such a window
--   - generalization: $\alpha\ge1+4/(1/2-\varepsilon_0)$ for some $\varepsilon_0<1/2$ with $0<\varepsilon\le\varepsilon_0$ → every $\alpha\ge9$ and every $0<\varepsilon<1/2$; reason: when $0<\varepsilon\le\varepsilon_0<1/2$, $1+4/(1/2-\varepsilon_0)>9$
--   - reading: $\widetilde O(F_{44})$ → $\le C\cdot F_{44}\cdot\log(\alpha d/\varepsilon)^m$; reason: at these parameters every suppressed logarithm is $O(\log(\alpha d/\varepsilon))$ (43)
--   - reading: a quantum algorithm with access to the oracle $|x\rangle|b\rangle\mapsto|x\rangle|b\oplus\nabla E(x)\rangle$ and its inverse (no model is defined) → unitaries on $\ell^2(\mathbb R^d\times\mathbb R^d\times W)$ interleaved with calls to the oracle $(x,b,w)\mapsto(x,b+\nabla E(x),w)$ or its inverse, then a basis measurement and classical post-processing; reason: the paper states no register precision; $\oplus$ on a real register is addition, and finite-precision registers and POVMs from basis measurements are covered
--   - reading: "let $E$ … there exists a quantum algorithm" → the algorithm is fixed from the class parameters before $E$ and takes $\beta$ as input; reason: Algorithm 2's inputs are $\beta,\varepsilon,s,\alpha,\xi,\rho$; an algorithm chosen per instance would make the statement trivial
--   - encoding: instances are Gibbs states $p=e^{-\beta E}/Z$ → instances are scaled potentials $V=\beta E$ with Gibbs state $e^{-V}/Z_V$; reason: two potentials with the same Gibbs state give the same oracle answers and the same target
--   - encoding: $[\beta E]_{s,\rho}\le\xi$ with the supremum over $x\in[0,2\pi)^d$, and $\beta\Delta\le\log\alpha$ → $|\partial^aV(x)|\,\rho^{\|a\|_1}\le\xi\,(a!)^s$ for every $a\ne0$ and every $x\in\mathbb R^d$, and $V(x)-V(y)\le\log\alpha$ for all $x,y$; reason: equivalent for a continuous $2\pi$-periodic $V$: its values and derivatives on $\mathbb R^d$ are those on the period cell, where the maximum and minimum are attained
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Proof of Theorem 1, Step 1, Eq. (44), p.16

import Mathlib
import Definitions.Def_GevreyGibbsSep_gibbs
import Definitions.Def_GevreyGibbsSep_tv
import Definitions.Def_GevreyGibbsSep_GibbsClass
import Definitions.Def_GevreyGibbsSep_FirstOrderQAlg
import Definitions.Def_GevreyGibbsSep_qOutputLaw
import Definitions.Def_GevreyGibbsSep_F44

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Eq. (44), proof of Theorem 1, Step 1, p.16 of arXiv:2608.24527 (sha256 d4fd40eb…): at
`ξ = 1/2` and `1/ρ = Θ(d^{1+s} α^{1/d} log^s α)`, the quantum query complexity is
`N_q ∈ Õ(α^{1/2+1/d} d^{5/2+s} (log α)^s (d + log α + log(1/ε))^s log²(1/ε))`.

**Formalization Note** For every window `c₀ X ≤ 1/ρ ≤ C₀ X`, `X = d^{1+s} α^{1/d} (log α)^s`,
there are `C > 0`, `m ∈ ℕ` (depending on `s, c₀, C₀`) such that for every integer `d > 2s`,
`α ≥ 9` and `0 < ε < 1/2` a first-order quantum algorithm, chosen before the instance, samples
every member of `W^s(α, 1/2, ρ)` at accuracy `ε` with at most `C · F44 · log(αd/ε)^m` queries. -/
theorem eq_44 :
    ∀ s : ℝ, 1 < s → ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ →
    ∃ C : ℝ, ∃ m : ℕ, 0 < C ∧
    ∀ d : ℕ, 2 * s < (d : ℝ) → ∀ α : ℝ, 9 ≤ α →
    ∀ ρ : ℝ, 0 < ρ →
      c₀ * ((d : ℝ) ^ (1 + s) * α ^ ((1 : ℝ) / d) * Real.log α ^ s) ≤ 1 / ρ →
      1 / ρ ≤ C₀ * ((d : ℝ) ^ (1 + s) * α ^ ((1 : ℝ) / d) * Real.log α ^ s) →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∃ (W : Type) (T : ℕ) (A : ℝ → FirstOrderQAlg d W T),
      (T : ℝ) ≤ C * F44 d s α ε * Real.log (α * d / ε) ^ m ∧
      ∀ β : ℝ, 0 < β → ∀ E : (Fin d → ℝ) → ℝ,
        (fun x => β * E x) ∈ GibbsClass d s α (1 / 2) ρ →
        tv (qOutputLaw (A β) E) (gibbs (fun x => β * E x)) ≤ ε := by sorry

end GevreyGibbsSep
