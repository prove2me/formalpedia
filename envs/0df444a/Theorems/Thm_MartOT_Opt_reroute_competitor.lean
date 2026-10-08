-- Prove2me | Theorems.Thm_MartOT_Opt_reroute_competitor
-- name    : MartOT.Opt.reroute_competitor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:26.750295+00:00
-- url     : https://prove2.me/theorems/52168fb8-bce4-47f0-8beb-a7e7ccf4cbab
-- title:
--   Proof of Theorem 6.1, p. 37 — the barycentre-preserving rerouting α′ of the three-point measure α is a competitor of α
-- statement:
--   Let $x,x',y^-,y^+,y'\in\mathbb R$ and $\lambda\in(0,1)$ with $\lambda y^+ + (1-\lambda)y^- = y'$. Let $\alpha$ be the measure on $\mathbb R\times\mathbb R$ that puts mass $\lambda$ on $(x,y^+)$, mass $1-\lambda$ on $(x,y^-)$ and mass $1$ on $(x',y')$, and let $\alpha'$ put mass $1-\lambda$ on $(x',y^-)$, mass $\lambda$ on $(x',y^+)$ and mass $1$ on $(x,y')$:
--
--   $$\alpha=\lambda\,\delta_{(x,y^+)}+(1-\lambda)\,\delta_{(x,y^-)}+\delta_{(x',y')},\qquad \alpha'=(1-\lambda)\,\delta_{(x',y^-)}+\lambda\,\delta_{(x',y^+)}+\delta_{(x,y')}.$$
--
--   Then $\alpha'$ is a competitor of $\alpha$ in the sense of Definition 1.10: the two measures have the same marginals and the same conditional barycentres in the second variable.
--
--   This is the rerouting by which the proof of Theorem 6.1 tests an optimal plan against the forbidden configuration of Figure 1.
--
--   **Formalization Note** The competitor relation is encoded by equality of both marginals and of $\int\rho(x)\,y\,d\alpha$ for every bounded measurable $\rho$ (the paper's device (4)). The orderings $x<x'$ and $y^-<y'<y^+$ of the page are not needed for this claim and are omitted, which makes the statement stronger. Masses are $\lambda$ and $1-\lambda$ as nonnegative extended reals.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 6.1, p. 37 (unnumbered: "Clearly, α′ is a competitor of α.")

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Opt

open MeasureTheory

theorem reroute_competitor (x x' ym yp y' l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (hcomb : l * yp + (1 - l) * ym = y') :
    MartOT.Var.IsCompetitor
      (ENNReal.ofReal l • Measure.dirac (x, yp) + ENNReal.ofReal (1 - l) • Measure.dirac (x, ym) +
        Measure.dirac (x', y'))
      (ENNReal.ofReal (1 - l) • Measure.dirac (x', ym) + ENNReal.ofReal l • Measure.dirac (x', yp) +
        Measure.dirac (x, y')) := by sorry

end MartOT.Opt
