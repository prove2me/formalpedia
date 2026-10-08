-- Prove2me | Theorems.Thm_FournierGuillin_Conc_eq_6
-- name    : FournierGuillin.Conc.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:22.035281+00:00
-- url     : https://prove2.me/theorems/b7261eb2-bdf4-4b5a-bd22-dc89412267c6
-- title:
--   Display (6), proof of Theorem 2, p. 19 — ℙ[V^p_N ≥ x/(2κ_{p,d})] ≤ a(N, x)1_{x≤A} under M_q(μ) < ∞, q > 2p
-- statement:
--   Let $d\ge1$, let $p>0$ with $p\ge d/2$ or $p\ge1$, let $q>2p$, and fix a value $M_0<\infty$. Put
--   $$V^p_N=\sum_{n\ge0}2^{pn}\mu(B_n)\,\mathcal D_p(\mathcal R_{B_n}\mu_N,\mathcal R_{B_n}\mu),$$
--   with $B_n$, $\mathcal R_{B_n}$ and the compact $\mathcal D_p$ of Notation 4. There are $A>0$ and $C,c>0$ such that for every $\mu\in\mathcal P(\mathbb R^d)$ with $M_q(\mu)=M_0$, all $N\ge1$ and all $x>0$,
--   $$\mathbb P\Big[V^p_N\ge\frac{x}{2\kappa_{p,d}}\Big]\le a(N,x)\mathbf 1_{\{x\le A\}},$$
--   where $\kappa_{p,d}=2^{p(1+d/2)}(2^p+1)/(2^p-1)$ and $a(N,x)=C e^{-cNx^2}$, $Ce^{-cN(x/\log(2+1/x))^2}$ or $Ce^{-cNx^{d/p}}$ according as $p>d/2$, $p=d/2$ or $p\in[1,d/2)$.
--
--   This handles the second term of the splitting $\mathcal D_p(\mu_N,\mu)\le Z^p_N+V^p_N$: the fluctuation of $\mu_N$ inside each shell, controlled by Proposition 10 applied to the rescaled measures.
--
--   **Formalization Note** The page proves (6) assuming only (3) ("We only assume (3) (which is implied by (1) or (2))"), so only (3) is a hypothesis. $A$, $C$, $c$ are quantified after $p,d,q$ and the moment value $M_0$ and before $\mu$, $N$, $x$. $V^p_N$ is valued in $[0,\infty]$. The range $p\ge d/2$ or $p\ge1$ is the one where $a(N,x)$ is printed in Theorem 2.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, proof of Theorem 2, p. 19, display (6) and the display defining V^p_N

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

/-- Display (6), proof of Theorem 2 (p. 19): under (3) (`M_q(μ) < ∞` for some `q > 2p`) there are
`A > 0` and `C, c > 0` (depending on `p, d, q` and `M_q(μ)`) such that for all `N ≥ 1` and `x > 0`,
`ℙ[V^p_N ≥ x/(2κ_{p,d})] ≤ a(N, x) 1_{x ≤ A}`. -/
theorem eq_6 (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p) (hrange : (d : ℝ) / 2 ≤ p ∨ 1 ≤ p)
    (q : ℝ) (hq : 2 * p < q) (M₀ : ℝ≥0∞) (hM₀ : M₀ < ⊤) :
    ∃ A C c : ℝ, 0 < A ∧ 0 < C ∧ 0 < c ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ], FournierGuillin.Moment.moment q μ = M₀ →
        ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
          Measure.pi (fun _ : Fin N => μ)
              {ω | ENNReal.ofReal (x / (2 * kappa d p)) ≤ Vp p μ ω} ≤
            ENNReal.ofReal (C * rateA d p c N x * (if x ≤ A then 1 else 0)) := by sorry

end FournierGuillin.Conc
