-- Prove2me | Theorems.Thm_LasserreFC_FinConv_theorem_2_4
-- name    : LasserreFC.FinConv.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:53.721998+00:00
-- url     : https://prove2.me/theorems/9771e9f6-8438-4861-8546-67497c1109f2
-- title:
--   Theorem 2.4 (Marshall), p. 5 — archimedean + BHC at every global minimizer ⇒ f − f_min ∈ I(V_ℝ(h)) + Q(g)
-- statement:
--   Let $V = V_{\mathbb R}(h)$, let $I(V) = \{q \in \mathbb R[x] : q(u) = 0 \ \forall u \in V\}$ be its vanishing ideal, and let $f_{\min}$ be the minimum of (1.1). If $\langle h\rangle + Q(g)$ is archimedean and the boundary hessian condition holds at every global minimizer of (1.1), then
--
--   $$f - f_{\min} \in I(V) + Q(g),$$
--
--   i.e. $f - f_{\min} = q + \sigma$ with $q$ vanishing on $V$ and $\sigma$ in the quadratic module $Q(g)$.
--
--   This is Marshall's theorem [16, Theorem 9.5.3], cited without proof in the paper; it is the representation step of the proof of Theorem 1.1.
--
--   **Formalization Note** "$\langle h\rangle + Q(g)$ is archimedean" is stated in the truncated form of p. 2, which is equivalent. $I(V)$ is Mathlib's `MvPolynomial.vanishingIdeal ℝ V`. The minimum is a real number that is the least value of $f$ on $K$ (this excludes $K = \emptyset$ only).
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 5, Theorem 2.4 (Marshall, [16, Theorem 9.5.3])

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_Hierarchy
import Definitions.Def_LasserreFC_FinConv_BHC

namespace LasserreFC.FinConv

open MvPolynomial

/-- Theorem 2.4 (Marshall), p. 5: if `⟨h⟩ + Q(g)` is archimedean and the boundary hessian condition
holds at every global minimizer of (1.1), then `f − f_min ∈ I(V_ℝ(h)) + Q(g)`. -/
theorem theorem_2_4 {n m1 m2 : ℕ} (P : POP n m1 m2) (harch : IsArchimedean P)
    (fmin : ℝ) (hfmin : IsLeast ((fun x => eval x P.f) '' P.K) fmin)
    (hbhc : ∀ u ∈ P.K, IsMinOn (fun x => eval x P.f) P.K u → IsBHC P u) :
    ∃ q ∈ vanishingIdeal ℝ (realVariety P), ∃ σ ∈ qmod P, P.f - C fmin = q + σ := by sorry

end LasserreFC.FinConv
