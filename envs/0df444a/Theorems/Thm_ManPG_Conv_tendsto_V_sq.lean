-- Prove2me | Theorems.Thm_ManPG_Conv_tendsto_V_sq
-- name    : ManPG.Conv.tendsto_V_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:37.262124+00:00
-- url     : https://prove2.me/theorems/6718b449-20dd-49af-b5fc-bc0c34199599
-- title:
--   Proof of Theorem 5.5 — along every ManPG run, lim_{k→∞} ‖V_k‖²_F = 0
-- statement:
--   Let $f,\nabla f,h$ satisfy the standing assumptions of problem (1.1) on $\mathcal M=\mathrm{St}(n,r)$, let $\mathrm{Retr}$ be a retraction with constants $M_1,M_2>0$ in (3.1)–(3.2), and let $\gamma\in(0,1)$, $t>0$. For every run $(X_k),(V_k),(\alpha_k)$ of Algorithm 1 (ManPG),
--   $$\lim_{k\to\infty}\|V_k\|_F^2=0.$$
--
--   This is the first display of the proof of Theorem 5.5. Combined with Lemma 5.3, it yields that every limit point of the iterates is stationary.
--
--   **Formalization Note** The paper derives this from "$F$ is bounded below on $\mathcal M$" and Lemma 5.2. Neither the lower bound nor a bound on $\nabla f$ is a hypothesis here. Both follow from the standing assumptions and the compactness of $\mathcal M$.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), p. 13, §5, proof of Theorem 5.5 (first display)

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic
import Definitions.Def_ManPG_Conv_Setting

open scoped Matrix
open Filter Topology ProjLikeRetr.Stiefel

namespace ManPG.Conv

/-- Proof of Theorem 5.5, p. 13: along any run of Algorithm 1 (any `γ ∈ (0, 1)`, `t > 0`),
`lim_{k→∞} ‖V_k‖_F² = 0`. -/
theorem tendsto_V_sq {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ)
    (R : Mat n r → Mat n r → Mat n r) (L Lh M1 M2 : ℝ)
    (hA : StandingAssumptions f gradf h L Lh) (hR : RetrBounds R M1 M2)
    (γ t : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t)
    (X V : ℕ → Mat n r) (α : ℕ → ℝ) (hrun : IsManPGRun f gradf h R γ t X V α) :
    Tendsto (fun k => frobNorm (V k) ^ 2) atTop (𝓝 0) := by sorry

end ManPG.Conv
