-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_Supplement_eq_16
-- name    : MaxSpectralRisk.Duality.Supplement.eq_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:16:14.343292+00:00
-- url     : https://prove2.me/theorems/10bb8ab9-c3fa-4c80-ac6d-d125ec8920d3
-- title:
--   (16) (used in the proof of Theorem 3) — finite dual vertex formula
-- statement:
--   Fix $\alpha\in(0,1)$ and a real loss matrix $L$ on two nonempty finite carriers. Let $P_\alpha(L)$ be the dual feasible polyhedron on page 19 with the normalization $\varphi_1=0$, and let $\mathcal V$ be its set of extreme points. Then $\mathcal V$ is finite and nonempty, depends only on $\alpha,L$, and for every pair of probability vectors $(\mu,\nu)\in K$,
--   $$
--   V_\alpha(\mu,\nu)=\min_{z=(\varphi,\psi,\rho,\beta)\in\mathcal V}
--   \bigl(\varphi\cdot\mu+\psi\cdot\nu+\beta\bigr).
--   $$
--   The minimum is attained. Here $V_\alpha$ is the primal maximum expected shortfall defined in (11), so the equality is the substantive dual representation, including finiteness. This supplies the active extreme points for Theorem 3.
--
--   Differences from the source:
--   - encoding: finite spaces admitting marginal probability distributions → Fin (m+1) and Fin (n+1), with the published IsDist predicate and K containing its boundary; reason: probability distributions force nonempty carriers; relabeling preserves all matrices and includes singleton carriers
--   - encoding: the enumeration k=1,...,N_D of all normalized dual extreme points → the finite nonempty set vertices alpha L, with an explicitly attained minimum; reason: enumeration does not affect the minimum and no arbitrary feasible point is substituted
--   - encoding: the finite MES value V_alpha of (11) → an EReal supremum of EReal infima of the published g, equated to a real attained dual objective; reason: complete-lattice extrema have no default values; the conclusion establishes finiteness and attainment
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 19, (16)

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Finite

namespace MaxSpectralRisk.Duality.Supplement

/-- (16), p. 19: the full set of normalized dual extreme points is finite,
nonempty and independent of the marginals. Its minimum is attained and equals
the MES value defined from (11), for every pair of probability vectors. -/
theorem eq_16 {m n : ℕ} (α : ℝ) (hα : 0 < α ∧ α < 1)
    (L : Fin (m + 1) → Fin (n + 1) → ℝ) :
    (vertices α L).Finite ∧ (vertices α L).Nonempty ∧
      ∀ θ ∈ (K : Set (Marginals m n)),
        ∃ z ∈ vertices α L, (∀ z' ∈ vertices α L, dualObjective z θ ≤ dualObjective z' θ) ∧
          finiteV α L θ = (dualObjective z θ : EReal) := by sorry

end MaxSpectralRisk.Duality.Supplement
