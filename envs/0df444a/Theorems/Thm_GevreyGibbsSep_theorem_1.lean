-- Prove2me | Theorems.Thm_GevreyGibbsSep_theorem_1
-- name    : GevreyGibbsSep.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:45:44.996434+00:00
-- url     : https://prove2.me/theorems/0d273a6a-9e0d-4869-82ad-ab46db53f658
-- title:
--   Theorem 1 — quantum–classical separation for continuous Gibbs sampling
-- statement:
--   Let $s>1$, $d>2s$, fix an accuracy cap $\varepsilon_0<\tfrac12$, and let the barrier amplitude satisfy $\alpha\ge1+4/(\tfrac12-\varepsilon_0)$. On the class of Gibbs states $\mathscr W^s_{\alpha,d}=\mathscr W^s(\alpha,\xi_{\alpha,d},\rho_{\alpha,d})$ with
--   $$\xi_{\alpha,d}=\frac12,\qquad\frac1{\rho_{\alpha,d}}=\Theta\big(d^{1+s}\alpha^{1/d}\log^s\alpha\big)$$
--   (implicit constants depending only on $s$), the following holds for every accuracy $0<\varepsilon\le\varepsilon_0$:
--
--   1. for every oracle order $k\in\mathbb N\cup\{\infty\}$, the classical query complexity obeys
--   $$N_{\mathrm{cl}}\ \ge\ \frac{1-2\varepsilon_0}{16}(\alpha-1);$$
--   2. there is a first-order quantum algorithm, with access to $O_{\nabla E}$ and its inverse, sampling every member of the class at accuracy $\varepsilon$ with query complexity (8) at $\xi=\xi_{\alpha,d}$, $\rho=\rho_{\alpha,d}$;
--   3. the ratio of the query complexities is
--   $$\frac{N_{\mathrm{cl}}}{N_q}=\widetilde\Omega\Big(\frac{\alpha^{c(d)}}{d^{\frac52+2s}\log^{s+2}\frac1\varepsilon}\Big),\qquad c(d)=\frac12-\frac1d,$$
--   with implicit constants depending only on $s$ and $\varepsilon_0$.
--
--   Classical samplers need a number of queries linear in the barrier amplitude, while a gradient-query quantum sampler needs about its square root: for $\log\alpha=\Omega(d)$ the separation is exponential in the dimension.
--
--   **Formalization Note** $\Theta$ is a window $c_0X\le1/\rho\le C_0X$, $X=d^{1+s}\alpha^{1/d}(\log\alpha)^s$, with $c_0,C_0$ from $s$ only, and every radius in it is covered. Clause 2 reads $T\le C_q\,F_8\,\log(\alpha d/\varepsilon)^{m_q}$ ($C_q,m_q$ from $s$ only). $N_q$ is the query count $T$ of that algorithm, and clause 3 reads $c_r\,G_{14}\,T/\log(\alpha d/\varepsilon)^{m_r}\le N_{\mathrm{cl}}$ ($c_r,m_r$ from $s,\varepsilon_0$), stated multiplicatively because $N_{\mathrm{cl}}$ may be infinite.
--
--   Differences from the source:
--   - reading: $1/\rho_{\alpha,d}=\Theta(d^{1+s}\alpha^{1/d}\log^s\alpha)$ with implicit constants depending only on $s$ → constants $0<c_0\le C_0$ from $s$ only, and the conclusions for every $\rho$ with $c_0X\le1/\rho\le C_0X$; reason: implies the statement for the paper's $\rho_{\alpha,d}$, which lies in such a window (42)
--   - reading: query complexity (8), $\widetilde O(F_8)$ → $T\le C_q\,F_8\,\log(\alpha d/\varepsilon)^{m_q}$ with $C_q,m_q$ depending only on $s$; reason: at these parameters every suppressed logarithm is $O(\log(\alpha d/\varepsilon))$ (43)
--   - reading: $N_{\mathrm{cl}}/N_q=\widetilde\Omega(G_{14})$ with constants depending on $s,\varepsilon_0$ → $c_r\,G_{14}\,T/\log(\alpha d/\varepsilon)^{m_r}\le N_{\mathrm{cl}}$ with $c_r>0$, $m_r$ depending on $s,\varepsilon_0$; reason: $\widetilde\Omega$ of a quantity that may be below $1$ is read with explicit polylogarithmic loss, as Step 2 (p.16) derives it; multiplicative because $N_{\mathrm{cl}}$ may be infinite
--   - reading: $N_q$ → the query count $T$ of the algorithm of clause 2; reason: the quantum algorithm whose existence the theorem asserts
--   - reading: a quantum algorithm with access to the oracle $|x\rangle|b\rangle\mapsto|x\rangle|b\oplus\nabla E(x)\rangle$ and its inverse (no model is defined) → unitaries on $\ell^2(\mathbb R^d\times\mathbb R^d\times W)$ interleaved with calls to the oracle $(x,b,w)\mapsto(x,b+\nabla E(x),w)$ or its inverse, then a basis measurement and classical post-processing; reason: the paper states no register precision; $\oplus$ on a real register is addition, and finite-precision registers and POVMs from basis measurements are covered
--   - reading: "let $E$ … there exists a quantum algorithm" → the algorithm is fixed from the class parameters before $E$ and takes $\beta$ as input; reason: Algorithm 2's inputs are $\beta,\varepsilon,s,\alpha,\xi,\rho$; an algorithm chosen per instance would make the statement trivial
--   - generalization: output maps $\Psi_n$, $n\ge1$ → an output $\widehat X_0$ with no query is also allowed; reason: a larger class of algorithms can only lower $N_{\mathrm{cl}}$, so the lower bound is at least as strong
--   - reading: a seed $\omega\sim P$ and maps $Q_n,\Psi_n$, with the output law the distribution over the seed → an arbitrary probability space of seeds and jointly measurable $Q_n,\Psi_n$; reason: the output law is only defined for measurable maps; the seed space is not restricted to countable ones
--   - encoding: instances are Gibbs states $p=e^{-\beta E}/Z$ → instances are scaled potentials $V=\beta E$ with Gibbs state $e^{-V}/Z_V$; reason: two potentials with the same Gibbs state give the same oracle answers and the same target
--   - encoding: $N_{\mathrm{cl}}\ge B$ in $\mathbb N\cup\{\infty\}$ → $\max(B,0)\le N_{\mathrm{cl}}$ in $[0,\infty]$; reason: the same inequality; a negative bound is trivially true in both
--   - encoding: the order-$k$ answer $\phi_k(p,x)=(\nabla^{\otimes j}\log\bar p(x))_{j=0}^{k}$ at a representative of $x$, $k\in\mathbb N\cup\{\infty\}$ → the family of all iterated partials $\partial_{i_1}\cdots\partial_{i_j}\log\bar p$ of every order $j$ at the $[0,2\pi)^d$ representative of $x$, with the entries of order $j>k$ set to $0$, and $k\in\mathbb N\cup\{\top\}$; reason: the entries of order $j\le k$ are the components of $\nabla^{\otimes j}\log\bar p(x)$ and the padded zeros carry no information, so every algorithm sees the same answers
--   - encoding: $[\beta E]_{s,\rho}\le\xi$ with the supremum over $x\in[0,2\pi)^d$, and $\beta\Delta\le\log\alpha$ → $|\partial^aV(x)|\,\rho^{\|a\|_1}\le\xi\,(a!)^s$ for every $a\ne0$ and every $x\in\mathbb R^d$, and $V(x)-V(y)\le\log\alpha$ for all $x,y$; reason: equivalent for a continuous $2\pi$-periodic $V$: its values and derivatives on $\mathbb R^d$ are those on the period cell, where the maximum and minimum are attained
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem 1, Eqs. (12)–(14), p.7; proof pp.16

import Mathlib
import Definitions.Def_GevreyGibbsSep_gibbs
import Definitions.Def_GevreyGibbsSep_tv
import Definitions.Def_GevreyGibbsSep_GibbsClass
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_Ncl
import Definitions.Def_GevreyGibbsSep_FirstOrderQAlg
import Definitions.Def_GevreyGibbsSep_qOutputLaw
import Definitions.Def_GevreyGibbsSep_F8
import Definitions.Def_GevreyGibbsSep_G14

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Theorem 1 (Separation), arXiv:2608.24527 (sha256 d4fd40eb…), Eqs. (12)–(14), p.7. Let
`s > 1`, `d > 2s`, `ε₀ < 1/2`, `α ≥ 1 + 4/(1/2 − ε₀)`, and consider `W^s_{α,d} = W^s(α, 1/2, ρ)`
with `1/ρ = Θ(d^{1+s} α^{1/d} log^s α)` (constants depending only on `s`). For every
`0 < ε ≤ ε₀`: (13) for every oracle order `k ∈ ℕ ∪ {∞}`, `N_cl ≥ ((1 − 2ε₀)/16)(α − 1)`;
a first-order quantum algorithm with query complexity (8) samples the class at accuracy `ε`; and
(14) `N_cl/N_q = Ω̃(α^{c(d)}/(d^{5/2+2s} log^{s+2}(1/ε)))`, `c(d) = 1/2 − 1/d`, with implicit
constants depending only on `s` and `ε₀`.

**Formalization Note** Readings: `Θ` is a window `c₀X ≤ 1/ρ ≤ C₀X` (constants from `s` only) and
every radius in it is covered; `Õ` in (8) is `≤ C_q · F8 · log(αd/ε)^{m_q}` (`C_q, m_q` from `s`
only); `N_q` is the query count `T` of that algorithm; `Ω̃` in (14) is
`N_cl ≥ c_r · G14 · T / log(αd/ε)^{m_r}` (`c_r, m_r` from `s, ε₀`). The quantum algorithm is
chosen before the instance and takes `β` as input. Instances are scaled potentials `V = βE`. -/
theorem theorem_1 :
    ∀ s : ℝ, 1 < s →
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧
    ∃ Cq : ℝ, ∃ mq : ℕ, 0 < Cq ∧
    ∀ ε₀ : ℝ, ε₀ < 1 / 2 →
    ∃ cr : ℝ, ∃ mr : ℕ, 0 < cr ∧
    ∀ d : ℕ, 2 * s < (d : ℝ) →
    ∀ α : ℝ, 1 + 4 / (1 / 2 - ε₀) ≤ α →
    ∀ ρ : ℝ, 0 < ρ →
      c₀ * ((d : ℝ) ^ (1 + s) * α ^ ((1 : ℝ) / d) * Real.log α ^ s) ≤ 1 / ρ →
      1 / ρ ≤ C₀ * ((d : ℝ) ^ (1 + s) * α ^ ((1 : ℝ) / d) * Real.log α ^ s) →
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      (∀ k : ℕ∞, ENNReal.ofReal ((1 - 2 * ε₀) / 16 * (α - 1))
          ≤ (Ncl d k (GibbsClass d s α (1 / 2) ρ) ε : ℝ≥0∞)) ∧
      ∃ (W : Type) (T : ℕ) (A : ℝ → FirstOrderQAlg d W T),
        (∀ β : ℝ, 0 < β → ∀ E : (Fin d → ℝ) → ℝ,
            (fun x => β * E x) ∈ GibbsClass d s α (1 / 2) ρ →
            tv (qOutputLaw (A β) E) (gibbs (fun x => β * E x)) ≤ ε) ∧
        (T : ℝ) ≤ Cq * F8 d s α (1 / 2) ρ ε * Real.log (α * d / ε) ^ mq ∧
        ∀ k : ℕ∞, ENNReal.ofReal (cr * G14 d s α ε / Real.log (α * d / ε) ^ mr * T)
            ≤ (Ncl d k (GibbsClass d s α (1 / 2) ρ) ε : ℝ≥0∞) := by sorry

end GevreyGibbsSep
