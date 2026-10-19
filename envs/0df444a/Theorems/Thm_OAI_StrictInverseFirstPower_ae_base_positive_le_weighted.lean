-- Prove2me | Theorems.Thm_OAI_StrictInverseFirstPower_ae_base_positive_le_weighted
-- name    : OAI.StrictInverseFirstPower.ae_base_positive_le_weighted
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:20:14.881818+00:00
-- url     : https://prove2.me/theorems/b4178e56-56a4-415b-9b15-9c64da9fd628
-- title:
--   Under an affine probability law, the positive Jacobian at the base point is at most its partner-weighted value (OpenAI strict inverse-first-power)
-- statement:
--   **Setting.** As in the statements `OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero` and `OAI.StrictInverseFirstPower.ae_bad_base_positive_zero` of this split: `DiskFamily` is the compact family of normalized univalent disk maps, $F = $ `halfPlaneFunction f` the half-plane model, $J_{F,+} = $ `jacobianPart k f true` the positive part of the Jacobian expression with parameter $k$, $V_F(z) = k\,y^{k-1}/|F'(z)|$ the critical height (`criticalHeight`), `sourcePairingDomain k` the rank-pairing domain, and `AffineProbabilityLaw μ β` the scaling identity $\int |Q_F(z)|\,\varphi(\texttt{rebase}\ f\ z)\,d\mu = y^{-\beta}\int\varphi\,d\mu$ for all $z \in \mathbb H$ and measurable $\varphi \ge 0$.
--
--   For $(f, z)$ in the pairing domain, `sourcePartner k (f, z)` is the point $w$ chosen by the pairing (a negative-Jacobian critical point over the same target, of the same descending rank, with $V_F(w) > V_F(z)$). The **partner ratio** is
--   $$\texttt{partnerRatio}\ k\ (f, z) = \Bigl(\frac{V_F(\texttt{sourcePartner}\ k\ (f, z))}{V_F(z)}\Bigr)^3 \quad\text{on the pairing domain}, \qquad 0 \text{ elsewhere}.$$
--
--   **Statement.** Let $\mu$ be a probability measure on `DiskFamily` and $\beta \ge 0$ a real number with `AffineProbabilityLaw μ β`, and put $k = (\beta + 2)/3$. Then for $\mu$-almost every $f$,
--   $$J_{F,+}(i) \;\le\; J_{F,+}(i)\cdot \texttt{partnerRatio}\ k\ (f, i),$$
--   as an inequality in $[0, \infty]$ (both sides read through `ENNReal.ofReal`). Here $i$ is the base point `UpperHalfPlane.I`.
--
--   This is the comparison $b \le A$ in the proof of the paper's Proposition 6.2 (strict weighted transport). Lean: `OAI.StrictInverseFirstPower.ae_base_positive_le_weighted`, OpenAI's lemma of that name (in `lean/OAI/Analysis/StrictMeans/StrictTransport.lean`). All definitions named here come from the definitions bundle `OAIQWSIFP000` of this split.
-- source:
--   OpenAI, A strict inverse-first-power bound for univalent functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/StrictMeans/StrictTransport.lean (declaration OAI.StrictInverseFirstPower.ae_base_positive_le_weighted)

import Mathlib
import Definitions.Def_OAIQWSIFP000

open Set Filter Metric Complex MeasureTheory OAI OAI.StrictInverseFirstPower
open scoped Topology ENNReal

theorem OAI.StrictInverseFirstPower.ae_base_positive_le_weighted (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    ∀ᵐ f ∂(μ : Measure DiskFamily),
      ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) ≤
      ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) *
        ENNReal.ofReal (partnerRatio ((β+2)/3) (f,UpperHalfPlane.I)) := by
  sorry
