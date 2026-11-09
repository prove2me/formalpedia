-- Prove2me | Theorems.Thm_GevreyGibbsSep_theorem_2
-- name    : GevreyGibbsSep.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:45:48.328233+00:00
-- url     : https://prove2.me/theorems/ffbd0f62-1017-4d07-8ec8-e5109bce5e62
-- title:
--   Theorem 2 — first-order quantum sampler with $\widetilde O(\sqrt{\alpha d}(\cdots)\log^2(1/\varepsilon))$ gradient queries
-- statement:
--   Let $s\ge1$, $d\ge1$, $\alpha\ge1$, $\xi,\rho>0$ and $0<\varepsilon<1/2$. There is a first-order quantum algorithm (taking the inverse temperature $\beta$ as input) such that for every Gibbs potential $E$ with $p=e^{-\beta E}/Z\in\mathscr W^s(\alpha,\xi,\rho)$ it returns a sample $X\sim\eta$ with $\mathrm{TV}(\eta,p)\le\varepsilon$ after
--   $$N_q\in\widetilde O\Big(\sqrt{\alpha d}\Big(1+\frac{d+\xi}{\rho}\Big[ds+\log\frac{\alpha(1+\xi/\rho)}{\varepsilon}\Big]^s\Big)\log^2\frac1\varepsilon\Big)$$
--   queries to the gradient oracle $O_{\nabla E}$ and its inverse, with implicit constants depending only on $s$.
--
--   The $\sqrt\alpha$ scaling is the quantum side of the separation.
--
--   **Formalization Note** $\widetilde O$: there are $C>0$ and $m\in\mathbb N$ depending only on $s$ with $N_q\le C\,F_8\,\Lambda^m$, $\Lambda=\log(e+d+\alpha+\xi+\rho+1/\rho+1/\varepsilon)$.
--
--   Differences from the source:
--   - reading: a quantum algorithm with access to the oracle $|x\rangle|b\rangle\mapsto|x\rangle|b\oplus\nabla E(x)\rangle$ and its inverse (no model is defined) → unitaries on $\ell^2(\mathbb R^d\times\mathbb R^d\times W)$ interleaved with calls to the oracle $(x,b,w)\mapsto(x,b+\nabla E(x),w)$ or its inverse, then a basis measurement and classical post-processing; reason: the paper states no register precision; $\oplus$ on a real register is addition, and finite-precision registers and POVMs from basis measurements are covered
--   - reading: "let $E$ … there exists a quantum algorithm" → the algorithm is fixed from the class parameters before $E$ and takes $\beta$ as input; reason: Algorithm 2's inputs are $\beta,\varepsilon,s,\alpha,\xi,\rho$; an algorithm chosen per instance would make the statement trivial
--   - reading: $N_q\in\widetilde O(F_8)$, implicit constants independent of $d,\alpha,\xi,\rho,\varepsilon$ for fixed $s$ → $N_q\le C\,F_8\,\Lambda^m$ with $C,m$ depending only on $s$, $\Lambda=\log(e+d+\alpha+\xi+\rho+1/\rho+1/\varepsilon)$; reason: footnote 1 (p.3) drops polylogarithmic factors; the suppressed factors (p.27, (A90)–(A94)) are polylogarithmic in these parameters
--   - encoding: instances are Gibbs states $p=e^{-\beta E}/Z$ → instances are scaled potentials $V=\beta E$ with Gibbs state $e^{-V}/Z_V$; reason: two potentials with the same Gibbs state give the same oracle answers and the same target
--   - encoding: $p\in\mathscr W^s(\alpha,\xi,\rho)$, $s\ge1$, dimension $d$ → hypotheses $s\ge1$, $\alpha\ge1$, $\xi,\rho>0$, $d\ge1$, $\beta>0$; reason: the ranges of Definition 2 and of the setting
--   - encoding: $[\beta E]_{s,\rho}\le\xi$ with the supremum over $x\in[0,2\pi)^d$, and $\beta\Delta\le\log\alpha$ → $|\partial^aV(x)|\,\rho^{\|a\|_1}\le\xi\,(a!)^s$ for every $a\ne0$ and every $x\in\mathbb R^d$, and $V(x)-V(y)\le\log\alpha$ for all $x,y$; reason: equivalent for a continuous $2\pi$-periodic $V$: its values and derivatives on $\mathbb R^d$ are those on the period cell, where the maximum and minimum are attained
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem 2, Eq. (24), pp.10–11; Theorem A.5, Eq. (A89), p.33

import Mathlib
import Definitions.Def_GevreyGibbsSep_gibbs
import Definitions.Def_GevreyGibbsSep_tv
import Definitions.Def_GevreyGibbsSep_GibbsClass
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_FirstOrderQAlg
import Definitions.Def_GevreyGibbsSep_qOutputLaw
import Definitions.Def_GevreyGibbsSep_F8

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Theorem 2 (= Theorem A.5), arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (24), pp.10–11 (and
(A89), p.33). For a Gibbs potential `E` with `p = e^{−βE}/Z ∈ W^s(α, ξ, ρ)`, `s ≥ 1`, there is a
quantum algorithm that returns a sample `X ∼ η` with `TV(η, p) ≤ ε` after
`N_q ∈ Õ(√(αd)(1 + ((d + ξ)/ρ)[ds + log(α(1 + ξ/ρ)/ε)]^s) log²(1/ε))` queries to `O_∇E` and its
inverse, for `0 < ε < 1/2`.

**Formalization Note** The algorithm is chosen from the class parameters `d, s, α, ξ, ρ, ε`
before the instance, and takes `β` as input (Algorithm 2, p.11); `E` enters only through the
oracle. `Õ` is read as: there are `C > 0`, `m ∈ ℕ` depending only on `s` with
`N_q ≤ C · F8 · Λ^m`, `Λ = log(e + d + α + ξ + ρ + 1/ρ + 1/ε)`. -/
theorem theorem_2 :
    ∀ s : ℝ, 1 ≤ s → ∃ C : ℝ, ∃ m : ℕ, 0 < C ∧
    ∀ d : ℕ, 0 < d → ∀ α ξ ρ ε : ℝ, 1 ≤ α → 0 < ξ → 0 < ρ → 0 < ε → ε < 1 / 2 →
    ∃ (W : Type) (T : ℕ) (A : ℝ → FirstOrderQAlg d W T),
      (T : ℝ) ≤ C * F8 d s α ξ ρ ε
          * Real.log (Real.exp 1 + d + α + ξ + ρ + 1 / ρ + 1 / ε) ^ m ∧
      ∀ β : ℝ, 0 < β → ∀ E : (Fin d → ℝ) → ℝ, (fun x => β * E x) ∈ GibbsClass d s α ξ ρ →
        tv (qOutputLaw (A β) E) (gibbs (fun x => β * E x)) ≤ ε := by sorry

end GevreyGibbsSep
