-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_prop_3_8
-- name    : NaiveFS.Multinomial.prop_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:38.681045+00:00
-- url     : https://prove2.me/theorems/cfb2ebd8-a347-452f-9ef0-de4e9a7c98ca
-- title:
--   Proposition 3.8, p. 12 — rounding an optimal (x, z) of (D) gives a feasible point at level k + |J| with ϕ(k) ≤ OPT ≤ ϕ(k + |J|)
-- statement:
--   Let $f^\pm\in\mathbb R^m$ with $f^\pm_i>0$ and $0<k<m$. Let $x$ (with $z=\mathbf 1-x$) be an optimal solution of the dual (D), and let $J=\{i:x_i\notin\{0,1\}\}$ be the set of indices where $x_i,z_i$ are not binary. Then there is a pair $(\theta^+,\theta^-)$ feasible for (SMNB) at sparsity level $\bar k=k+|J|$ whose objective value $\mathrm{OPT}=f^{+\top}\log\theta^++f^{-\top}\log\theta^-$ satisfies
--   $$\phi(k)\le\mathrm{OPT}\le\phi(k+|J|),$$
--   and moreover $\mathrm{OPT}$ is at least the optimal value of (D).
--
--   Combined with a solution of (D) with few fractional coordinates, this turns the relaxation into a near-optimal sparse classifier.
--
--   **Formalization Note** (D) is the corrected dual of Proposition 3.7 (without the term $-(x^\top g)$). The last conclusion, $D(x)\le\mathrm{OPT}$, is what the proof establishes ("by concavity of the objective"); it is stated because the printed chain alone is met by a maximizer of $\phi(k)$ itself and would carry no information about $x$. The page's three vectors $\bar\theta,\bar\theta^+,\bar\theta^-$ are the form (29); in (SMNB) form $\theta^\pm_i=\bar\theta^\pm_i$ where $\bar x_i=1$ and $\theta^+_i=\theta^-_i=\bar\theta_i$ where $\bar z_i=1$. $k<m$ is the standing assumption of §3.1.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 12, Proposition 3.8; proof pp. 12–13

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model
import Definitions.Def_NaiveFS_Multinomial_Dual

open Finset

namespace NaiveFS.Multinomial

/-- Proposition 3.8, p. 12. Given `k > 0` and an optimal solution `x` (`z = 1 − x`) of the
(corrected) dual (D), let `J = {i : xᵢ ∉ {0,1}}`. There is a point feasible for (SMNB) at level
`k + |J|` whose objective value `OPT` satisfies `ϕ(k) ≤ OPT ≤ ϕ(k + |J|)`; moreover
`OPT` is at least the optimal value of (D), as the proof establishes. -/
theorem prop_3_8 {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (hk : 0 < k) (hkm : k < m)
    (x : Fin m → ℝ) (hx : DFeasible k x) (hxopt : ∀ x', DFeasible k x' → Dobj fp fm x' ≤ Dobj fp fm x) :
    ∃ θp θm : Fin m → ℝ,
      Feasible (k + (univ.filter (fun i => x i ≠ 0 ∧ x i ≠ 1)).card) θp θm ∧
      phi fp fm k ≤ objective fp fm θp θm ∧
      objective fp fm θp θm ≤ phi fp fm (k + (univ.filter (fun i => x i ≠ 0 ∧ x i ≠ 1)).card) ∧
      Dobj fp fm x ≤ objective fp fm θp θm := by sorry

end NaiveFS.Multinomial
