-- Prove2me | Theorems.Thm_OAI_StrictInverseFirstPower_good_targets_bad_source_mass_zero
-- name    : OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:20:17.111235+00:00
-- url     : https://prove2.me/theorems/a6a42b1e-1dc6-4186-b3b0-fd0069a6c9b6
-- title:
--   Positive-Jacobian source mass outside the pairing domain vanishes when almost every target is good (OpenAI strict inverse-first-power)
-- statement:
--   **Setting.** `DiskFamily` is the set of normalized univalent disk maps: continuous $f : \mathbb D \to \mathbb C$ ($\mathbb D$ the open unit disk) whose extension by $0$ outside $\mathbb D$ is holomorphic and injective on $\mathbb D$, with $f(0) = 0$ and $f'(0) = 1$ (`DiskNormalized`). For $f$ in the family, $F = $ `halfPlaneFunction f` is its half-plane model, $F(z) = 2i\, f\bigl((z - i)/(z + i)\bigr)$. Points of the upper half-plane $\mathbb H$ are written $z = x + iy$ with $y > 0$. For a real $k$ define:
--   - the logarithmic derivative $q_F(z) = -i\,y\,F''(z)/F'(z)$ (`logarithmicDerivative`);
--   - the Jacobian expression $J_F(z) = \bigl(k(k-1) + (2k-1)\,\mathrm{Re}\,q_F(z) + |q_F(z)|^2\bigr)/k^2$ (`jacobianExpression k F z`) and its positive part $J_{F,+}(z) = \max(J_F(z), 0)$ (`jacobianPart k f true z`);
--   - the critical map $G_F(z) = F(z) - i\,y\,F'(z)/k$ (`criticalMap`) and the critical height $V_F(z) = k\,y^{k-1}/|F'(z)|$ (`criticalHeight`).
--
--   A pair $(f, \xi)$ with $\xi \in \mathbb C$ is **good** (`GoodPair k (f, ξ)`) when (i) for every $h > 0$ the set $\{z : y > 0,\ |F(z) - \xi| \le y^k/h\}$ is compact; (ii) $J_F(z) \ne 0$ at every $z \in \mathbb H$ with $G_F(z) = \xi$; and (iii) distinct points $z, w \in \mathbb H$ with $G_F(z) = G_F(w) = \xi$ have distinct critical heights.
--
--   The **pairing domain** `sourcePairingDomain k` is the set of pairs $(f, z) \in$ `DiskFamily` $\times\, \mathbb H$ for which, with $\xi = G_F(z)$: the pair $(f, \xi)$ is good, $J_F(z) > 0$, and there is $w \in \mathbb H$ with $G_F(w) = \xi$, $J_F(w) < 0$, $V_F(z) < V_F(w)$, such that $w$ has the same descending rank among the negative-Jacobian points of the fiber $G_F^{-1}(\xi)$ as $z$ among its positive-Jacobian points (`RankPairRelation`). The descending rank of a point is the number of points of its sign class with strictly larger critical height (`criticalRank`, `descendingRank`). `badSourceTest k` is the indicator of the complement of the pairing domain.
--
--   Finally, for real $\beta$, the positive source mass density is
--   $$\texttt{sourceMassDensity}\ \beta\ k\ f\ \texttt{true}\ z = y^{\beta - 1}\,|Q_F(z)|\,J_{F,+}(z), \qquad Q_F(z) = 1/F'(z) \ (\texttt{halfPlaneQ}),$$
--   read in $[0, \infty]$. Write `upperArea` for Lebesgue measure on $\mathbb H$.
--
--   **Statement.** Let $\beta$ and $k$ be real numbers with $0 < k$, and let $f$ be in `DiskFamily`. If $(f, \xi)$ is good for Lebesgue-almost every $\xi \in \mathbb C$, then
--   $$\int_{\mathbb H} y^{\beta - 1}\,|Q_F(z)|\,J_{F,+}(z)\;\mathbf 1\bigl[(f, z) \notin \texttt{sourcePairingDomain}\ k\bigr]\; d\,\texttt{upperArea}(z) = 0,$$
--   a lower Lebesgue integral of $[0, \infty]$-valued functions.
--
--   This is the fixed-map step of the paper's Lemma 6.1 (goodness at the normalized point). Lean: `OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero`, OpenAI's lemma of that name (in `lean/OAI/Analysis/StrictMeans/NormalizedTargets.lean`). All definitions named here come from the definitions bundle `OAIQWSIFP000` of this split.
-- source:
--   OpenAI, A strict inverse-first-power bound for univalent functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-inverse-first-power-bound-for-univalent-functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/StrictMeans/NormalizedTargets.lean (declaration OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero)

import Mathlib
import Definitions.Def_OAIQWSIFP000

open Set Filter Metric Complex MeasureTheory OAI OAI.StrictInverseFirstPower
open scoped Topology ENNReal

theorem OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero {β k : ℝ} (hk : 0 < k) (f : DiskFamily)
    (hg : ∀ᵐ ξ : ℂ, GoodPair k (f,ξ)) :
    (∫⁻ z, sourceMassDensity β k f true z * badSourceTest k (f,z) ∂upperArea) = 0 := by
  sorry
