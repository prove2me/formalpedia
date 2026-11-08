-- Prove2me | Theorems.Thm_GibbsCongestion_proposition_2_4
-- name    : GibbsCongestion.proposition_2_4
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:02:14.376575+00:00
-- url     : https://prove2.me/theorems/c50489fc-34f3-4680-8548-5c864b8ecc4e
-- title:
--   Proposition 2.4 (Brändén and Huh): SLC is preserved by non-negative scaling
-- statement:
--   If $p\in\mathbb R[x_1,\dots,x_n]$ is strongly log-concave and $\gamma\in\mathbb R_{\ge0}$, then $\gamma p$ is strongly log-concave.
--
--   It is used to pass between the generating polynomial (11), its normalization $\frac1{n!}g$, and the normalized distribution $\pi'$.
--
--   **Formalization Note** Variables are indexed by an arbitrary finite type $\sigma$; strong log-concavity is required on the open positive orthant (Definition 2.2).
--
--   Differences from the source:
--   - reading: log-concave on a subset S ⊆ ℝⁿ≥0 (S unspecified) → log-concave on the open positive orthant; reason: the convention of the cited works (Anari et al.; Brändén–Huh)
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Proposition 2.4, p.10

import Mathlib
import Definitions.Def_GibbsCongestion_IsSLC

namespace GibbsCongestion

/-- **Proposition 2.4** (Brändén and Huh) (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Proposition 2.4, p.10). If `p` is
strongly log-concave and `γ ≥ 0`, then `γ p` is strongly log-concave. -/
theorem proposition_2_4 {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (hp : IsSLC p)
    (γ : ℝ) (hγ : 0 ≤ γ) : IsSLC (MvPolynomial.C γ * p) := by sorry

end GibbsCongestion
