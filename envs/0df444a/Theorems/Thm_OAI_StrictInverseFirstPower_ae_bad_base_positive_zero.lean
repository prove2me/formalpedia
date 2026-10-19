-- Prove2me | Theorems.Thm_OAI_StrictInverseFirstPower_ae_bad_base_positive_zero
-- name    : OAI.StrictInverseFirstPower.ae_bad_base_positive_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:20:13.102911+00:00
-- url     : https://prove2.me/theorems/a79613b0-34c8-49c6-a09c-ebb810a9d8d4
-- title:
--   Under an affine probability law, the positive Jacobian at the base point vanishes off the pairing domain (OpenAI strict inverse-first-power)
-- statement:
--   **Setting.** As in the statement `OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero` of this split: `DiskFamily` is the compact family of normalized univalent disk maps $f$ ($f(0) = 0$, $f'(0) = 1$), $F = $ `halfPlaneFunction f` its half-plane model $F(z) = 2i\,f\bigl((z-i)/(z+i)\bigr)$ on the upper half-plane $\mathbb H$, $Q_F = 1/F'$ (`halfPlaneQ`), $J_F$ the Jacobian expression with parameter $k$ (`jacobianExpression`), $J_{F,+} = \max(J_F, 0)$ (`jacobianPart k f true`), and `sourcePairingDomain k` the set of pairs $(f, z)$ at which a positive-Jacobian critical point is paired by rank with a strictly higher negative-Jacobian one over a good target.
--
--   For $z = x + iy \in \mathbb H$, `rebase f z` is the member of the family whose half-plane model is
--   $$w \mapsto \frac{F(x + y\,w) - F(z)}{y\,F'(z)}$$
--   (the affine rebasing $T_z F$ of the paper). For a probability measure $\mu$ on `DiskFamily` and a real $\beta$, the **affine probability law** condition `AffineProbabilityLaw μ β` says: for every $z \in \mathbb H$ and every measurable $\varphi : $ `DiskFamily` $\to [0, \infty]$,
--   $$\int |Q_F(z)|\;\varphi(\texttt{rebase}\ f\ z)\;d\mu(f) = y^{-\beta} \int \varphi\; d\mu,$$
--   as lower Lebesgue integrals in $[0, \infty]$, with $y^{-\beta}$ the real power.
--
--   **Statement.** Let $\mu$ be a probability measure on `DiskFamily` and $\beta \ge 0$ a real number with `AffineProbabilityLaw μ β`, and put $k = (\beta + 2)/3$. Then for $\mu$-almost every $f$: if $(f, i) \notin$ `sourcePairingDomain k`, then $J_{F,+}(i) = 0$.
--
--   Here $i$ is the base point `UpperHalfPlane.I`. This is the paper's Lemma 6.1 (goodness at the normalized point), in almost-sure form. Lean: `OAI.StrictInverseFirstPower.ae_bad_base_positive_zero`, OpenAI's lemma of that name (in `lean/OAI/Analysis/StrictMeans/StrictTransport.lean`). All definitions named here come from the definitions bundle `OAIQWSIFP000` of this split.
-- source:
--   OpenAI, A strict inverse-first-power bound for univalent functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/StrictMeans/StrictTransport.lean (declaration OAI.StrictInverseFirstPower.ae_bad_base_positive_zero)

import Mathlib
import Definitions.Def_OAIQWSIFP000

open Set Filter Metric Complex MeasureTheory OAI OAI.StrictInverseFirstPower
open scoped Topology ENNReal

theorem OAI.StrictInverseFirstPower.ae_bad_base_positive_zero (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), (f,UpperHalfPlane.I)∉sourcePairingDomain ((β+2)/3) →
      jacobianPart ((β+2)/3) f true UpperHalfPlane.I = 0 := by
  sorry
