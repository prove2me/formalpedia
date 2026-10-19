-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_lemma_11
-- name    : HTInsensBW.PhaseType.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:25.623597+00:00
-- url     : https://prove2.me/theorems/b8dfeafe-fe4c-47c4-b2e4-1e436f9f6849
-- title:
--   Lemma 11, p. 39 — the matrix M of the constructed inner product is well defined and positive definite
-- statement:
--   Let every route $r$ have a file-size law $(\pi_r,S_r)$ in the class $\mathcal D$, a weight $\kappa_r>0$ and a base arrival rate $\lambda^{(0)}_r>0$. For every route $r$ and phases $k_1,k_2$, the function
--   $$\sigma\mapsto\frac{P_{k_1}(\sigma)P_{k_2}(\sigma)}{\pi_r(-S_r)^{-1}\exp(S_r\sigma)\mathbf 1},\qquad\mathbf P(\sigma)=\exp(S_r\sigma)\mathbf 1,$$
--   is integrable on $(0,\infty)$, so the matrix $M_r$ of (67) is well defined, and $M_r$ is positive definite. Consequently the block-diagonal matrix $M=\operatorname{diag}(M_1,\dots,M_R)$ is positive definite, and $\langle\mathbf y,\mathbf z\rangle=\mathbf y^TM\mathbf z$ is an inner product on $\mathbb R^K$.
--
--   This validates the inner product on which all the drift arguments of §6 rest.
--
--   **Formalization Note** "Well-defined" is read as in the proof (p. 39): every entry integral converges. The integrability clause is part of the statement because a non-integrable integrand would have Bochner integral $0$ in Lean.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 39, Lemma 11 (Appendix C); (65)–(67), p. 24

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **Lemma 11, p. 39 — the inner product `M` is well defined and positive definite.**
(Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 39, Lemma 11; definition (65)–(67), p. 24.)
For every route `r`, every entry integrand of `M_r` in (67) is integrable on `(0, ∞)` (so `M_r` is
well defined), and `M_r` is positive definite; consequently the block-diagonal `M` is positive
definite.

**Formalization Note** "Well-defined" is read as the proof reads it (p. 39): the entrywise integrals
converge. Without that clause a non-integrable integrand would have Bochner integral `0`. The
hypotheses `κ_r > 0`, `λ^(0)_r > 0` are the standing ones (pp. 5, 7); the class `D` structure
(distinct block rates, positive first-phase mass) is in `PhaseTypeD`. -/
theorem lemma_11 {L R : ℕ} (N : BWNetwork L R)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r) :
    (∀ r, (∀ k₁ k₂ : Phase (N.D r),
        IntegrableOn (Mintegrand (N.D r) k₁ k₂) (Set.Ioi (0 : ℝ))) ∧ (Mr N r).PosDef) ∧
      (Mfull N).PosDef := by sorry

end HTInsensBW.PhaseType
