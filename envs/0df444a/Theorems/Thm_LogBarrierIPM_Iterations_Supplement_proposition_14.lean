-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_proposition_14
-- name    : LogBarrierIPM.Iterations.Supplement.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:16:37.51163+00:00
-- url     : https://prove2.me/theorems/a7eef22c-3e9f-4c71-b79a-6b91adc3186b
-- title:
--   Proposition 14 — bounded product sublevels (corrected: dual sign)
-- statement:
--   Assume strict primal-dual feasibility over $K$. Let $z^*=(x^*,w^*,s^*,y^*)$ be any optimal pair, $\boldsymbol\mu>0$ and $\lambda=\operatorname{val}(\boldsymbol\mu)$. Then
--   $$F^\lambda=P^\lambda\times Q^\lambda\quad\text{is a bounded tropical polyhedron},$$
--   where $P^\lambda=\{(x,w)\in\operatorname{val}(\mathcal P):\langle s^*,x\rangle_{\mathbb T}\oplus\langle y^*,w\rangle_{\mathbb T}\le\lambda\}$ and $Q^\lambda$ is the corresponding dual sublevel using $(x^*,w^*)$. Moreover $\operatorname{val}(z)\in F^\lambda$ for every solution $z$ of (17) at $\boldsymbol\mu$, that is, for $z=\mathcal C(\boldsymbol\mu)$. Stars inside tropical products denote their valuations. The proposition furnishes the barycenter used in Theorem 15.
--
--   Differences from the source:
--   - correction: the displayed dual says maximize bᵀy → minimize bᵀy, equivalently maximize -bᵀy; reason: the gap on pp. 14–15 is cᵀx+bᵀy; Proposition 14 uses bᵀy+ν≥0, and the central-path barrier on p. 4 already has -bᵀy
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: 1-based finite vectors and the tropical semiring → 0-based Fin vectors and WithBot real coordinates; reason: the index shift preserves every coordinate, including bottom values
--   - encoding: the point C(μ) → every solution z of (17), quantified inside clause (ii) only; reason: the solution is unique and exists (p. 14, concluded in Theorem 15); clause (i) does not depend on it
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 15, Proposition 14

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_TropicalLP

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem proposition_14 {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (hstrict : StrictlyFeasibleK A b c)
    (zstar : PuiseuxSlackPoint n m) (hopt : OptimalPairK A b c zstar)
    (μ : Puiseux) (hμ : KPositive μ) :
    (tropicalSublevel A b c μ.val =
      {q | ∃ u ∈ primalSublevel A b zstar μ.val,
        ∃ v ∈ dualSublevel A c zstar μ.val, q = Fin.append u v}) ∧
    (IsTropicalPolyhedron (tropicalSublevel A b c μ.val) ∧
      TropicalBounded (tropicalSublevel A b c μ.val)) ∧
    ∀ z : PuiseuxSlackPoint n m, IsCentralK A b c μ z →
      valPoint z ∈ tropicalSublevel A b c μ.val := by sorry

end LogBarrierIPM.Iterations.Supplement
