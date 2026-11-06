-- Prove2me | Theorems.Thm_GradSuffice_appendix_E_2
-- name    : GradSuffice.appendix_E_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:52.538801+00:00
-- url     : https://prove2.me/theorems/a1e7851b-a35e-45d4-a0b9-983e39452627
-- title:
--   Appendix E.2, pp.48–49 — M-type $p$ of $B^\star$ gives a bounded $q$-uniformly convex regularizer, $q=p/(p-1)$ (corrected: constant $K(p,C)$ for the printed $(1/C)^q$)
-- statement:
--   Let $B$ be the unit ball of a Banach space $X$, let $1<p\le2$, and let $q=p/(p-1)$ be the conjugate exponent.
--
--   **Appendix E.2 (M-type implies uniform convexity).** If $B^\star$ has M-type $p$ with constant $C$, there is a convex function $R$ on $B$ with $0\le R\le1$ that is $(K,q)$-uniformly convex for a constant $K>0$ depending only on $p$ and $C$:
--   $$R\Big(\frac{w_1+w_2}2\Big)\le\frac12R(w_1)+\frac12R(w_2)-\Big(\frac1K\Big)^q\Big\|\frac{w_1-w_2}2\Big\|^q\qquad(w_1,w_2\in B),$$
--   and $R$ is continuous on $B$.
--
--   The appendix builds a $p$-uniformly smooth function on the dual from the M-type inequality (Pisier's construction) and passes to its conjugate. This is the implication 4 → 5 of Theorem 1.
--
--   Differences from the source:
--   - reading: q-uniform convexity of R⋆ (q not defined in E.2) → q = p/(p − 1); reason: E.2 obtains R⋆ by duality from a p-uniformly smooth function; the dual exponent is the conjugate one
--   - correction: the displayed constant (1/C)^q → (1/K)^q for some K > 0 depending only on p and C; reason: the display is false for the R⋆ that E.2 constructs: in a Hilbert space with p = q = 2, B⋆ has M-type 2 with constant C = 1 (in both normalizations, (3) and (50)), (50) gives R(ξ) = ‖ξ‖², so R⋆(w) = ‖w‖²/4, whose midpoint gap is (1/4)‖(w₁ − w₂)/2‖², not ‖(w₁ − w₂)/2‖²; E.2 also uses C for two normalizations (C^p in (50), C in (3)); the §2 Theorem (ii), p.6, states the constant as K depending on the parameters, which is what Theorem 1 (4 → 5) uses
--   - generalization: R⋆ convex, non-negative and bounded, q-uniformly convex → additionally continuous on B, with 0 ≤ R ≤ 1 on B; reason: continuity is what Theorem 1 item 5 and the §2 Theorem (ii) assert for this regularizer; dropping it gives E.2's conclusion
--   - encoding: (1/K)^q ‖(w₁ − w₂)/2‖^q → NondualOpt.IsUnifConvexOn B R ((1/(2K))^q) q; reason: ‖(w₁ − w₂)/2‖^q = (1/2)^q ‖w₁ − w₂‖^q
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), App. E.2, pp.48–49 (implication 4 → 5 of Theorem 1, p.8)

import Mathlib
import Definitions.Def_NondualOpt_IsUnifConvexOn
import Definitions.Def_GradSuffice_HasMType

namespace GradSuffice

/-- **Appendix E.2 (M-type implies uniform convexity).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, App. E.2, pp.48–49: from M-type `p` of
`B⋆` with constant `C` the appendix builds `R` (Eq. (50)), shows it is `p`-uniformly smooth, and
concludes: "By duality, we obtain `q`-uniform convexity of `R⋆`: `R⋆((w₁+w₂)/2) ≤ (1/2)R⋆(w₁) +
(1/2)R⋆(w₂) − (1/C)^q ‖(w₁−w₂)/2‖^q` […] Therefore, `R⋆` is non-negative with `R(0) = 0` and bounded."
This is the implication 4 → 5 of Theorem 1 (p.8: "The implication 4→5 follows from the
martingale-type and uniform-convexity results of Enflo [17], Pisier [36]. For completeness, we repeat
it in Appendix E.2").

**Formalization Note.** `q = p/(p−1)` is the conjugate exponent. The uniform-convexity constant is a
`K > 0` depending only on `p` and `C` (chosen before the space), written in the `(K, q)` form of p.5,
i.e. `NondualOpt.IsUnifConvexOn B R ((1/(2K))^q) q`. The printed constant `(1/C)^q` is corrected to
this `K`: it fails for E.2's own `R⋆` in a Hilbert space (`p = q = 2`, M-type constant `C = 1`, (50)
gives `R(ξ) = ‖ξ‖²`, `R⋆(w) = ‖w‖²/4`, midpoint gap `(1/4)‖(w₁−w₂)/2‖²`). "Bounded" and "non-negative" are `0 ≤ R ≤ 1` on
`B`; continuity on `B` is the "continuous convex function" of the §2 Theorem (ii) and of Theorem 1
item 5. -/
theorem appendix_E_2 :
    ∀ p C : ℝ, 1 < p → p ≤ 2 → ∃ K : ℝ, 0 < K ∧
      ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X], HasMType X p C →
        ∃ R : X → ℝ, ContinuousOn R (Metric.closedBall (0 : X) 1) ∧ ConvexOn ℝ (Metric.closedBall (0 : X) 1) R ∧
          (∀ w ∈ Metric.closedBall (0 : X) 1, 0 ≤ R w ∧ R w ≤ 1) ∧
          NondualOpt.IsUnifConvexOn (Metric.closedBall (0 : X) 1) R ((1 / (2 * K)) ^ (p / (p - 1))) (p / (p - 1)) := by sorry

end GradSuffice
