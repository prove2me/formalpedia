-- Prove2me | Theorems.Thm_GevreyGibbsSep_theorem_4
-- name    : GevreyGibbsSep.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:45:29.524194+00:00
-- url     : https://prove2.me/theorems/f948daca-c705-49de-baa7-2e536784827a
-- title:
--   Theorem 4 — classical lower bound $N_{\mathrm{cl}}\ge\frac{1-2\varepsilon_0}{16}(\alpha-1)$
-- statement:
--   Let $s>1$. There are constants $0<c_0\le C_0$ depending only on $s$ such that the following holds. Let $d>2s$ be an integer, fix an accuracy level $\varepsilon_0<1/2$, let the barrier amplitude satisfy
--   $$\alpha\ge1+\frac{4}{1/2-\varepsilon_0},$$
--   and take class parameters $\xi_{\alpha,d}=\tfrac12$ and $\rho$ with
--   $$c_0X\le\frac1\rho\le C_0X,\qquad X=d^{1+s}\alpha^{1/d}(\log\alpha)^s,$$
--   i.e. $1/\rho_{\alpha,d}=\Theta(d^{1+s}\alpha^{1/d}\log^s\alpha)$. Then for every $0<\varepsilon\le\varepsilon_0$ and every oracle order $k\in\mathbb N\cup\{\infty\}$,
--   $$N_{\mathrm{cl}}\big(\mathscr W^s(\alpha,\tfrac12,\rho),\varepsilon\big)\ \ge\ \frac{1-2\varepsilon_0}{16}(\alpha-1).$$
--
--   Every classical sampler, with queries of any order, needs a number of queries linear in the barrier amplitude.
--
--   Differences from the source:
--   - reading: there are class parameters with $1/\rho_{\alpha,d}=\Theta(d^{1+s}\alpha^{1/d}\log^s\alpha)$, implicit constants depending only on $s$ → constants $0<c_0\le C_0$ depending only on $s$, and the bound for every $\rho$ with $c_0X\le1/\rho\le C_0X$; reason: this implies the existence of such parameters; by monotonicity (Remark 3) the bound holds for every radius below $\rho_{\alpha,d}$
--   - generalization: output maps $\Psi_n$, $n\ge1$ → an output $\widehat X_0$ with no query is also allowed; reason: a larger class of algorithms can only lower $N_{\mathrm{cl}}$, so the lower bound is at least as strong
--   - reading: a seed $\omega\sim P$ and maps $Q_n,\Psi_n$, with the output law the distribution over the seed → an arbitrary probability space of seeds and jointly measurable $Q_n,\Psi_n$; reason: the output law is only defined for measurable maps; the seed space is not restricted to countable ones
--   - encoding: instances are Gibbs states $p=e^{-\beta E}/Z$ → instances are scaled potentials $V=\beta E$ with Gibbs state $e^{-V}/Z_V$; reason: two potentials with the same Gibbs state give the same oracle answers and the same target
--   - encoding: $N_{\mathrm{cl}}\ge B$ in $\mathbb N\cup\{\infty\}$ → $\max(B,0)\le N_{\mathrm{cl}}$ in $[0,\infty]$; reason: the same inequality; a negative bound is trivially true in both
--   - encoding: the order-$k$ answer $\phi_k(p,x)=(\nabla^{\otimes j}\log\bar p(x))_{j=0}^{k}$ at a representative of $x$, $k\in\mathbb N\cup\{\infty\}$ → the family of all iterated partials $\partial_{i_1}\cdots\partial_{i_j}\log\bar p$ of every order $j$ at the $[0,2\pi)^d$ representative of $x$, with the entries of order $j>k$ set to $0$, and $k\in\mathbb N\cup\{\top\}$; reason: the entries of order $j\le k$ are the components of $\nabla^{\otimes j}\log\bar p(x)$ and the padded zeros carry no information, so every algorithm sees the same answers
--   - encoding: $[\beta E]_{s,\rho}\le\xi$ with the supremum over $x\in[0,2\pi)^d$, and $\beta\Delta\le\log\alpha$ → $|\partial^aV(x)|\,\rho^{\|a\|_1}\le\xi\,(a!)^s$ for every $a\ne0$ and every $x\in\mathbb R^d$, and $V(x)-V(y)\le\log\alpha$ for all $x,y$; reason: equivalent for a continuous $2\pi$-periodic $V$: its values and derivatives on $\mathbb R^d$ are those on the period cell, where the maximum and minimum are attained
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem 4, Eqs. (35)–(37), pp.14–15; proof pp.15–16

import Mathlib
import Definitions.Def_GevreyGibbsSep_GibbsClass
import Definitions.Def_GevreyGibbsSep_Ncl

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Theorem 4 (classical lower bound), arXiv:2608.24527 (sha256 d4fd40eb…), Eqs. (35)–(37),
pp.14–15. For `s > 1` there are constants `0 < c₀ ≤ C₀` depending only on `s` such that for every
integer `d > 2s`, every `ε₀ < 1/2`, every `α ≥ 1 + 4/(1/2 − ε₀)` and every `ρ` with
`c₀ X ≤ 1/ρ ≤ C₀ X`, `X = d^{1+s} α^{1/d} (log α)^s` (that is, `ξ_{α,d} = 1/2` and
`1/ρ_{α,d} = Θ(d^{1+s} α^{1/d} log^s α)`), for every `0 < ε ≤ ε₀` and every order `k`:
`N_cl(W^s(α, 1/2, ρ), ε) ≥ ((1 − 2ε₀)/16)(α − 1)`.

**Formalization Note** The `Θ` of (36) is read as a window of radii fixed by constants depending
only on `s`, and the bound is claimed for every radius in the window (this implies the paper's
"there are class parameters"). -/
theorem theorem_4 :
    ∀ s : ℝ, 1 < s →
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧
    ∀ d : ℕ, 2 * s < (d : ℝ) →
    ∀ ε₀ : ℝ, ε₀ < 1 / 2 →
    ∀ α : ℝ, 1 + 4 / (1 / 2 - ε₀) ≤ α →
    ∀ ρ : ℝ, 0 < ρ →
      c₀ * ((d : ℝ) ^ (1 + s) * α ^ ((1 : ℝ) / d) * Real.log α ^ s) ≤ 1 / ρ →
      1 / ρ ≤ C₀ * ((d : ℝ) ^ (1 + s) * α ^ ((1 : ℝ) / d) * Real.log α ^ s) →
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ k : ℕ∞,
      ENNReal.ofReal ((1 - 2 * ε₀) / 16 * (α - 1))
        ≤ (Ncl d k (GibbsClass d s α (1 / 2) ρ) ε : ℝ≥0∞) := by sorry

end GevreyGibbsSep
