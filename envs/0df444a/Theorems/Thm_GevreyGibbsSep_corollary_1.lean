-- Prove2me | Theorems.Thm_GevreyGibbsSep_corollary_1
-- name    : GevreyGibbsSep.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:45:07.830208+00:00
-- url     : https://prove2.me/theorems/459d3697-e946-4cf8-9a3f-69842b040571
-- title:
--   Corollary 1 — $N_{\mathrm{cl}}(\mathscr W^s(\alpha,\xi,\rho),\varepsilon)\ge(2\pi/\ell)^d(\delta-\varepsilon)-1$
-- statement:
--   Let $s>1$, $0<\ell<2\pi$, $0<\nu\le\ell/4$ and $\alpha>e$, and put $M=(2\pi/\ell)^d$, $S=(\alpha-1)(1-2\nu/\ell)^d$, $\delta(\nu,\ell,\alpha)=(1+S)/(M+S)$ and $\rho_E(\nu,\ell,\alpha)=\mathfrak r_s\nu/(2d^s(\log\alpha)^s)$. For every $\xi\ge\xi_E=1/2$, every $0<\rho\le\rho_E(\nu,\ell,\alpha)$, every oracle order $k\in\mathbb N\cup\{\infty\}$ and every accuracy $\varepsilon<\delta(\nu,\ell,\alpha)$,
--   $$N_{\mathrm{cl}}\big(\mathscr W^s(\alpha,\xi,\rho),\varepsilon\big)\ \ge\ \Big(\frac{2\pi}{\ell}\Big)^d\big(\delta(\nu,\ell,\alpha)-\varepsilon\big)-1 .$$
--
--   The geometry $(\nu,\ell)$ of the hidden mesa is left free; Theorem 4 fixes it.
--
--   Differences from the source:
--   - encoding: $\ell<2\pi$ (Definition 4 adds $0<\ell$), dimension $d$ → hypotheses $0<\ell<2\pi$ and $d\ge1$; reason: the ranges of Definition 4 and the paper's standing dimension
--   - encoding: $\rho\le\rho_E$ with the class of Definition 2 ($\rho>0$) → $0<\rho\le\rho_E$; reason: Definition 2 requires $\rho>0$
--   - generalization: accuracy $\varepsilon<\delta$ with $\varepsilon>0$ (Definition 3) → every real $\varepsilon<\delta$; reason: for $\varepsilon\le0$, $N_{\mathrm{cl}}=\infty$ and the statement is true
--   - generalization: output maps $\Psi_n$, $n\ge1$ → an output $\widehat X_0$ with no query is also allowed; reason: a larger class of algorithms can only lower $N_{\mathrm{cl}}$, so the lower bound is at least as strong
--   - reading: a seed $\omega\sim P$ and maps $Q_n,\Psi_n$, with the output law the distribution over the seed → an arbitrary probability space of seeds and jointly measurable $Q_n,\Psi_n$; reason: the output law is only defined for measurable maps; the seed space is not restricted to countable ones
--   - encoding: instances are Gibbs states $p=e^{-\beta E}/Z$ → instances are scaled potentials $V=\beta E$ with Gibbs state $e^{-V}/Z_V$; reason: two potentials with the same Gibbs state give the same oracle answers and the same target
--   - encoding: $N_{\mathrm{cl}}\ge B$ in $\mathbb N\cup\{\infty\}$ → $\max(B,0)\le N_{\mathrm{cl}}$ in $[0,\infty]$; reason: the same inequality; a negative bound is trivially true in both
--   - encoding: the order-$k$ answer $\phi_k(p,x)=(\nabla^{\otimes j}\log\bar p(x))_{j=0}^{k}$ at a representative of $x$, $k\in\mathbb N\cup\{\infty\}$ → the family of all iterated partials $\partial_{i_1}\cdots\partial_{i_j}\log\bar p$ of every order $j$ at the $[0,2\pi)^d$ representative of $x$, with the entries of order $j>k$ set to $0$, and $k\in\mathbb N\cup\{\top\}$; reason: the entries of order $j\le k$ are the components of $\nabla^{\otimes j}\log\bar p(x)$ and the padded zeros carry no information, so every algorithm sees the same answers
--   - encoding: $[\beta E]_{s,\rho}\le\xi$ with the supremum over $x\in[0,2\pi)^d$, and $\beta\Delta\le\log\alpha$ → $|\partial^aV(x)|\,\rho^{\|a\|_1}\le\xi\,(a!)^s$ for every $a\ne0$ and every $x\in\mathbb R^d$, and $V(x)-V(y)\le\log\alpha$ for all $x,y$; reason: equivalent for a continuous $2\pi$-periodic $V$: its values and derivatives on $\mathbb R^d$ are those on the period cell, where the maximum and minimum are attained
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Corollary 1, Eq. (34), p.14; proof in Appendix B 3 d, p.46

import Mathlib
import Definitions.Def_GevreyGibbsSep_GibbsClass
import Definitions.Def_GevreyGibbsSep_Ncl
import Definitions.Def_GevreyGibbsSep_rs

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Corollary 1 (classical sampling lower bounds over `W^s(α, ξ, ρ)`), arXiv:2608.24527 (sha256
d4fd40eb…), Eq. (34), p.14. For `s > 1`, `0 < ℓ < 2π`, `0 < ν ≤ ℓ/4`, `α > e`, every `ξ ≥ 1/2`,
every `0 < ρ ≤ ρ_E(ν, ℓ, α) = r_s ν/(2 d^s (log α)^s)`, every order `k` and every
`ε < δ(ν, ℓ, α) = (1 + S)/(M + S)` (with `M = (2π/ℓ)^d`, `S = (α − 1)(1 − 2ν/ℓ)^d`):
`N_cl(W^s(α, ξ, ρ), ε) ≥ (2π/ℓ)^d (δ(ν, ℓ, α) − ε) − 1`.

**Formalization Note** `d ≥ 1` is the paper's standing dimension; `ρ > 0` is required by
Definition 2. -/
theorem corollary_1 {d : ℕ} (hd : 0 < d) (s α ν ℓ ξ ρ ε : ℝ) (hs : 1 < s)
    (hℓ : 0 < ℓ) (hℓ2 : ℓ < 2 * Real.pi) (hν : 0 < ν) (hνℓ : ν ≤ ℓ / 4) (hα : Real.exp 1 < α)
    (hξ : 1 / 2 ≤ ξ) (hρ : 0 < ρ) (hρE : ρ ≤ rs s * ν / (2 * (d : ℝ) ^ s * Real.log α ^ s))
    (k : ℕ∞)
    (hε : ε < (1 + (α - 1) * (1 - 2 * (ν / ℓ)) ^ d)
              / ((2 * Real.pi / ℓ) ^ d + (α - 1) * (1 - 2 * (ν / ℓ)) ^ d)) :
    ENNReal.ofReal ((2 * Real.pi / ℓ) ^ d *
        ((1 + (α - 1) * (1 - 2 * (ν / ℓ)) ^ d)
            / ((2 * Real.pi / ℓ) ^ d + (α - 1) * (1 - 2 * (ν / ℓ)) ^ d) - ε) - 1)
      ≤ (Ncl d k (GibbsClass d s α ξ ρ) ε : ℝ≥0∞) := by sorry

end GevreyGibbsSep
