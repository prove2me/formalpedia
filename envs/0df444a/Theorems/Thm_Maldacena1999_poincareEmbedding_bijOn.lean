-- Prove2me | Theorems.Thm_Maldacena1999_poincareEmbedding_bijOn
-- name    : Maldacena1999.poincareEmbedding_bijOn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:17:16.332855+00:00
-- url     : https://prove2.me/theorems/70a8d160-9bd1-4ab8-9244-a2e5ced1b0d0
-- title:
--   Poincaré coordinates: bijection $\{U>0\}\to\{X\in\mathrm{AdS}_{p+2}: X_{-1}+X_{p+1}>0\}$
-- statement:
--   Let $p\ge0$ and $R>0$, and let $\Phi_R:(U,x)\mapsto X$ be the Poincaré parametrisation of eq. (A.2) (see the definitions file). Then $\Phi_R$ restricts to a bijection
--   $$\Phi_R:\ \{(U,x)\in\mathbb R\times\mathbb R^{1,p} : U>0\}\ \xrightarrow{\ \sim\ }\ \{X\in\mathrm{AdS}_{p+2}(R) : X_{-1}+X_{p+1}>0\}.$$
--   That is, $\Phi_R$ maps the half-space $U>0$ into this region, is injective there, and every point of the hyperboloid with $X_{-1}+X_{p+1}>0$ is $\Phi_R(U,x)$ for some $U>0$ and $x$.
--
--   This makes precise the paper's remark that the region $U>0$ outside the horizon is exactly one part of the hyperboloid (A.1).
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://doi.org/10.1023/A:1026654312961 (arXiv:hep-th/9711200), Appendix, eq. (A.2) and the paragraph after (A.3), p. 1130

import Mathlib
import Definitions.Def_Maldacena1999_Defs

open Filter Topology

namespace Maldacena1999

theorem poincareEmbedding_bijOn (p : ℕ) (R : ℝ) (hR : 0 < R) :
    Set.BijOn (poincareEmbedding p R) {q | 0 < q.1}
      {X | X ∈ AdS p R ∧ 0 < X 0 + X (Fin.last (p + 2))} := by
  sorry

end Maldacena1999
