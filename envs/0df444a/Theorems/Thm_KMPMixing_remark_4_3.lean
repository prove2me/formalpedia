-- Prove2me | Theorems.Thm_KMPMixing_remark_4_3
-- name    : KMPMixing.remark_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:26.60885+00:00
-- url     : https://prove2.me/theorems/c2202450-992d-41b5-ba8e-0a3717a406ac
-- title:
--   Remark 4.3 — $M^{(t,G)}_{\mathrm{LKMP}}=\mathbb E_{e,p}[A^{\otimes t}]$
-- statement:
--   Let $G=(V=[d],E)$ be a connected graph on $d\ge2$ vertices and $t$ a positive integer. Let $A=A_{e,p}$ be the random row-stochastic matrix of Eq. (8) built from a uniformly random edge $e\in E$ and an independent $p\sim\mathrm{Unif}[0,1]$. Then the transition matrix of the labeled chain is $M^{(t,G)}_{\mathrm{LKMP}}=\mathbb E_{e,p}[A^{\otimes t}]$, that is, for all $x,y\in\Omega_G$,
--   $$
--   M^{(t,G)}_{\mathrm{LKMP}}(x,y)=\frac1{|E|}\sum_{e\in E}\int_0^1\prod_{\ell=1}^tA_{e,p}(x_\ell,y_\ell)\,dp.
--   $$
--
--   This rewrites the uniform split of Definition 3.3 as independent moves of the particles given $(e,p)$, which is the source of the conditional product structure.
--
--   Differences from the source:
--   - encoding: a connected graph $G$ on $d$ vertices, $t$ positive (standing assumptions of Definition 4.2) → hypotheses `G.Connected`, `2 ≤ d`, `0 < t`; reason: with $d=1$ there is no edge and the chain is not defined
--   - encoding: the matrix identity $M=\mathbb E_{e,p}[A^{\otimes t}]$ → an entrywise identity with a finite average over $E$ and $\int_0^1dp$, $A^{\otimes t}(x,y)=\prod_\ell A(x_\ell,y_\ell)$; reason: the same expectation
-- source:
--   Chen et al., arXiv:2609.38044, Remark 4.3, p.19 (PDF p.21); Observation 4.1, p.18

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
import Definitions.Def_KMPMixing_auxMatrix
open MarkovMixing

namespace KMPMixing

/-- **Remark 4.3** (arXiv:2609.38044, p.19 (PDF p.21); with Observation 4.1, p.18). Let `A` be the
random row-stochastic matrix of Eq. (8) built from a uniformly random edge `e = {i, j} ∈ E` and an
independent `p ∼ Unif[0, 1]`. The transition matrix of the labeled chain is
`M^{(t,G)}_LKMP = E_{e,p}[A^{⊗t}]`, i.e. for all `x, y ∈ Ω_G`,
`M_LKMP(x, y) = (1/|E|) Σ_{e ∈ E} ∫_0^1 ∏_{ℓ=1}^t A_{e,p}(x_ℓ, y_ℓ) dp`.

**Formalization Note** `A^{⊗t}(x, y) = ∏_ℓ A(x_ℓ, y_ℓ)`. The standing assumptions of §4
(Definition 4.2: `G` connected on `d` vertices, `t` positive) are hypotheses, with `d ≥ 2`. -/
theorem remark_4_3 {d : ℕ} (hd : 2 ≤ d) (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (hG : G.Connected) (t : ℕ) (ht : 0 < t) (x y : Fin t → Fin d) :
    labeledChain G t x y =
      ((edgePairs G).card : ℝ)⁻¹ *
        ∑ e ∈ edgePairs G, ∫ p in (0 : ℝ)..1, ∏ ℓ, auxMatrix e.1 e.2 p (x ℓ) (y ℓ) := by sorry

end KMPMixing
