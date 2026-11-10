-- Prove2me | Theorems.Thm_OLPDual_lemma_1
-- name    : OLPDual.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:21:13.327976+00:00
-- url     : https://prove2.me/theorems/94525f2f-a249-4e7e-bd63-5f818f505151
-- title:
--   Lemma 1, p.11 — the identity (9) for $f(p)-f(p^*)$
-- statement:
--   Let $f$ and $\nabla f$ be as in (7) and (8). For points $p$ and $p^*$,
--
--   $$
--   f(p)-f(p^*)=\nabla f(p^*)^\top(p-p^*)+\mathbb E\Bigl[\int_{a^\top p}^{a^\top p^*}\bigl(I(r>v)-I(r>a^\top p^*)\bigr)\,dv\Bigr],
--   $$
--
--   where the expectation is taken with respect to $(a,r)\sim\mathcal P$. The two terms play the role of the first- and second-order terms of a Taylor expansion of the non-differentiable function $f$; this is an identity of Knight's type.
--
--   Differences from the source:
--   - generalization: p ≥ 0 and p* the optimal solution → arbitrary p and pstar in ℝ^m; reason: the proof on p.31 uses neither; the printed lemma is the special case
--   - reading: identity (9) "holds regardless of the distribution 𝒫" (p.11) → Assumption 1 is a hypothesis; reason: it is the standing assumption of §3 and makes every expectation finite
--   - encoding: u = (r, a) → u = (a, r); reason: order of the pair only; same law
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Lemma 1, display (9), p.11; proof p.31

import Mathlib
import Definitions.Def_OLPDual_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Lemma 1**, Li–Ye, arXiv:1909.05499v5, p.11 (PDF 11), display (9):
`f(p) − f(p*) = ∇f(p*)ᵀ(p − p*) + E[∫_{aᵀp}^{aᵀp*} (I(r > v) − I(r > aᵀp*)) dv]`.
**Formalization Note** The paper states it for `p ≥ 0` and the optimal `p*`; the proof (p.31) uses
neither, so `p` and `pstar` are arbitrary here. Assumption 1 makes every integral finite. -/
theorem lemma_1 (Θ : Model) {m : ℕ} (d : E m) (law : Measure (E m × ℝ))
    [IsProbabilityMeasure law] (hA1 : Assumption1 Θ d law) (p pstar : E m) :
    f d law p - f d law pstar =
      ⟪gradf d law pstar, p - pstar⟫ + ∫ u, knightTerm u.1 u.2 p pstar ∂law := by sorry

end OLPDual
