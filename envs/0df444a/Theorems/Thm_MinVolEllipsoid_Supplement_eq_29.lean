-- Prove2me | Theorems.Thm_MinVolEllipsoid_Supplement_eq_29
-- name    : MinVolEllipsoid.Supplement.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:34:23.70381+00:00
-- url     : https://prove2.me/theorems/dbb166b1-ef8a-4381-9a6c-c86a802cce05
-- title:
--   Display (29) — strong duality for the scaled maximum volume inscribed ellipsoid problem (28)
-- statement:
--   Let $\mathcal P=\{x\in\mathbb R^K:Sx\le t\}$, $S\in\mathbb R^{J\times K}$, $t\in\mathbb R^J$, be compact, convex and with nonempty interior (Assumption 1). Consider the scaled maximum volume inscribed ellipsoid problem
--
--   $$
--   \sup_{B\in\mathbb S^K,\ d\in\mathbb R^K}\ \log\det(B)\quad\text{s.t.}\quad\|BS_{j:}\|+K S_{j:}^\top d\le Kt_j\ \ \forall j\in[J] \tag{28}
--   $$
--
--   and its Lagrange dual
--
--   $$
--   \inf\ K\rho^\top t-K-\log\det\Bigl(-\tfrac12\bigl(S^\top\Lambda+\Lambda^\top S\bigr)\Bigr)\quad\text{s.t.}\quad \Lambda\in\mathbb R^{J\times K},\ \rho\in\mathbb R^J,\ S^\top\rho=0,\ \|\Lambda_{j:}\|\le\rho_j\ \ \forall j\in[J]. \tag{29}
--   $$
--
--   Then strong duality holds: the optimal value of (29) equals the optimal value of (28), which is $\log\mathrm{Vol}(\mathcal E_{\mathrm{smvie}})$.
--
--   Here $S_{j:}$ and $\Lambda_{j:}$ are the transposed $j$-th rows, $\|\cdot\|$ is the Euclidean norm, and the domains of $\log\det$ are the positive definite matrices. The proof of Theorem 3 starts from this identity.
--
--   **Formalization Note** Both optimal values are extended reals (`MinVolEllipsoid.Supplement.dual29Value` and `MinVolEllipsoid.Supplement.logVolSmvie`), and the statement is their equality.
--
--   Differences from the source:
--   - reading: "the objective function of (29) is the logarithm of Vol(ℰ_smvie)" for the polytope of Appendix B.1 → the optimal value of (29) equals the optimal value of (28), assuming Assumption 1 for {Sx ≤ t}; reason: Assumption 1 is the paper's standing assumption (p.1), and the Slater point of p.31 is built from a point in the interior of 𝒫.
--   - encoding: optimal values of (28) and (29) → `EReal`-valued supremum and infimum over the domains of log det; reason: Lean convention, no junk values; same instances.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Appendix B.1, displays (28)–(29), p.31

import Mathlib
import Definitions.Def_MinVolEllipsoid_Supplement_polytope
import Definitions.Def_MinVolEllipsoid_Supplement_logVolSmvie
import Definitions.Def_MinVolEllipsoid_Supplement_dual29Value

namespace MinVolEllipsoid.Supplement

/-- **Display (29): strong duality for the scaled maximum volume inscribed ellipsoid problem**
(Mittal & Hanasusanto, arXiv:1807.07507v4, Appendix B.1, displays (28)–(29), p.31: "The Lagrange
dual of (28) is given by (29) … To show that strong duality holds, a Slater point can be constructed
… Therefore, the objective function of (29) is the logarithm of Vol(ℰ_smvie).").

Let `𝒫 = {x ∈ ℝᴷ : Sx ≤ t}` satisfy Assumption 1 (compact, convex, full-dimensional). Then the
optimal value of the dual

`inf Kρ⊤t − K − log det(−½(S⊤Λ + Λ⊤S))  s.t. Λ ∈ ℝ^{J×K}, ρ ∈ ℝᴶ, S⊤ρ = 0, ‖Λ_{j:}‖ ≤ ρ_j ∀ j`  (29)

equals the optimal value of (28), `sup { log det B : ‖B S_{j:}‖ + K S_{j:}⊤d ≤ K t_j ∀ j }`, which
is `log Vol(ℰ_smvie)`.

**Formalization Note** Both optimal values are `EReal`-valued (`dual29Value`, `logVolSmvie`), so the
equality is between genuine extended-real optimal values; the domains of `log det` are the positive
definite matrices. Assumption 1 is the paper's standing assumption (p.1) for (27)–(29), whose proof
of strong duality uses a point in the interior of `𝒫`. -/
theorem eq_29 {n m : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ)
    (hPc : IsCompact (polytope S t)) (hPcv : Convex ℝ (polytope S t))
    (hPi : (interior (polytope S t)).Nonempty) :
    dual29Value S t = logVolSmvie S t := by sorry

end MinVolEllipsoid.Supplement
