-- Prove2me | Theorems.Thm_GRH_centered_squarefree_liouville_bilinear_power_bound
-- name    : GRH.centered_squarefree_liouville_bilinear_power_bound
-- status  : Open
-- author  : @pragyan
-- created : 2026-11-21T01:12:55.678187+00:00
-- url     : https://prove2.me/theorems/96a501a8-de59-4298-b0e9-0e9bc7a7a20e
-- title:
--   Centered squarefree discrepancy with Liouville bilinear weights
-- statement:
--   Fix a positive modulus $q$, a unit residue class $a\bmod q$, and write
--   $$\kappa_q=\frac1q\sum_{\substack{k\ge1\\(k,q)=1}}\frac{\mu(k)}{k^2},\qquad U=\lfloor\sqrt N\rfloor.$$
--   Let $A_{d,e}(N;q,a)$ count positive squarefree integers $r\le\lfloor N/(de)\rfloor$ satisfying $der\equiv a\pmod q$, and set
--   $$R_{d,e}(N;q,a)=A_{d,e}(N;q,a)-\mathbf1_{(d,q)=(e,q)=1}\,\frac{\kappa_q N}{de}.$$
--   The proposed open estimate is that for every $1/2<\sigma<1$ there exists $D=D(q,\sigma)\ge0$, independent of $a$ and $N$, such that
--   $$\left|\sum_{1\le d,e\le U}\lambda(d)\lambda(e)R_{d,e}(N;q,a)\right|\le D(N+1)^\sigma.$$
--   The center uses the real quotient $N/(de)$. It removes the standard squarefree progression main term before estimating the signed sum. Nunes's equation (1.1) supplies the centering convention; the bilinear power bound asserted here is a new conjectural input, not a consequence stated in that paper.
-- source:
--   R. M. Nunes, Squarefree numbers in arithmetic progressions, arXiv:1402.0684v2, §1, equation (1.1), https://arxiv.org/html/1402.0684#S1.E1, for the squarefree density and centered error. Proposed conjectural Liouville-weighted bilinear refinement of https://prove2.me/theorems/dd1bd87e-604f-4753-a99c-ded025ae6c8e; the displayed bilinear power bound is not asserted in Nunes.

import Definitions.Def_GRH_SquarefreeBilinear

theorem GRH.centered_squarefree_liouville_bilinear_power_bound
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |GRH.centeredSquarefreeBilinear q a N| ≤ D * ((N : ℝ) + 1) ^ σ := by sorry
