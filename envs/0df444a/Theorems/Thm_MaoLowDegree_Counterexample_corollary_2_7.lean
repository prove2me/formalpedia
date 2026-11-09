-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_corollary_2_7
-- name    : MaoLowDegree.Counterexample.corollary_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:02.718973+00:00
-- url     : https://prove2.me/theorems/08a35e3f-fd59-4937-8d2e-1ad941de5e74
-- title:
--   Corollary 2.7 — vanishing advantage and likelihood-ratio projection
-- statement:
--   Fix the construction parameters, a valid constructed family $P_n$, and $n\ge n_0$. For every integer $0\le d\le D_\star$, let $\mathcal L_n=dP_n/dQ_n$ and let $\mathcal L_n^{\le d}$ denote its real degree-$d$ orthogonal projection. Then all three conclusions hold:
--   $$\operatorname{Adv}_{\le d}(P_n,Q_n)=0,\qquad \mathcal L_n^{\le d}=1,\qquad \|\mathcal L_n^{\le d}\|_{L^2(Q_n)}=1.$$
--
--   The projection equality is pointwise on the finite cube, equivalent to equality in $L^2(Q_n)$ because $Q_n$ has full support. This states the entire corollary, including the constant norm and the degree-zero boundary.
--
--   Differences from the source:
--   - encoding: the fixed subspace, basis, points and planted family of Sections 2–3 → CodeData, Construction and ValidConstruction with explicit standing numerical hypotheses; reason: expands the section preamble without assuming a graph-law conclusion
--   - encoding: real L²(Q) orthogonal projection → finite Walsh expansion and referenced finite L² sum; reason: the uniform null has full support and Walsh characters span the same real degree space
--   - encoding: integers 0 <= d <= D_star → natural degree d bounded by D_star; reason: these are exactly the source nonnegative integer degrees
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Corollary 2.7, p.11

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Corollary 2.7, p.11. All three conclusions are retained. -/
theorem corollary_2_7 (r : ℕ) (β₁ β₂ b κ : ℝ)
    (hparams : Admissible r β₁ β₂ b κ) (C : Construction r b κ)
    (hC : ValidConstruction β₁ C) (n : ℕ) (hn : C.n₀ ≤ n)
    (d : ℕ) (hd : d ≤ starDegree r b κ n) :
    advantage (constructedFamily C n) d = 0 ∧
      lowDegreeProjection (constructedFamily C n) d = (fun _ => 1) ∧
      l2Norm (lowDegreeProjection (constructedFamily C n) d) = 1 := by sorry

end MaoLowDegree.Counterexample
