-- Prove2me | Theorems.Thm_GPSAnalysis_Core_kkt_of_conforming
-- name    : GPSAnalysis.Core.kkt_of_conforming
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:01:18.95418+00:00
-- url     : https://prove2.me/theorems/b3a67880-b69a-45a7-817b-797f3c8e8f9d
-- title:
--   Theorem 3.14 — KKT conditions at limits of refining subsequences under conforming directions
-- statement:
--   Consider a GPS run satisfying A1 ($f_\Omega(x_0)<\infty$), A2 ($A$ rational) and A3 (all iterates lie in a compact set). Let $\hat x$ be the limit of a refining subsequence, let $f$ be Lipschitz near $\hat x$ and strictly differentiable at $\hat x$ with strict gradient $\nabla f(\hat x)$, and suppose that the rule selecting the poll sets $D_k=D(k,x_k)\subseteq D$ conforms to $\Omega$ for some $\epsilon>0$ (Definition 3.13). Then
--
--   $$\nabla f(\hat x)^T w\ \ge\ 0\quad\text{for all } w\in T_\Omega(\hat x),\qquad\text{and}\qquad -\nabla f(\hat x)\in N_\Omega(\hat x).$$
--
--   Thus $\hat x$ is a KKT point of the linearly constrained problem. This recovers the Lewis–Torczon convergence result for linearly constrained pattern search under a weaker smoothness assumption.
--
--   **Formalization Note** $f=g$ on a neighbourhood $U$ of $\hat x$ with $g$ real-valued and Lipschitz on $U$ (the standing assumption of Section 3.4), and strict differentiability is the directional notion of Section 3.4. $T_\Omega$ and $N_\Omega$ are defined as on p. 900 of the paper.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 901, Theorem 3.14

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run
import Definitions.Def_GPSAnalysis_Core_Clarke
import Definitions.Def_GPSAnalysis_Core_Cones

open Filter Topology

namespace GPSAnalysis.Core

/-- Theorem 3.14 (Audet–Dennis 2003, p. 901). Under A1–A3, let `x̂` be the limit of a refining
subsequence, let `f` be Lipschitz near `x̂` and strictly differentiable at `x̂` with strict
gradient `∇f(x̂)`, and let the poll sets `D_k` conform to `Ω` for some `ε > 0`. Then
`∇f(x̂)ᵀ w ≥ 0` for all `w ∈ T_Ω(x̂)` and `-∇f(x̂) ∈ N_Ω(x̂)`. -/
theorem kkt_of_conforming {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA2 : AssumptionA2 P) (hA3 : AssumptionA3 R)
    (K : ℕ → ℕ) (hK : IsRefiningSubseq R K) (xhat : Fin n → ℝ)
    (hlim : Tendsto (fun i => R.x (K i)) atTop (𝓝 xhat))
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 xhat) (g : (Fin n → ℝ) → ℝ)
    (hfg : ∀ y ∈ U, P.f y = (g y : WithTop ℝ)) (L : NNReal) (hL : LipschitzOnWith L g U)
    (grad : Fin n → ℝ) (hgrad : HasStrictDirGradAt g grad xhat)
    (ε : ℝ) (hε : 0 < ε) (hconf : ConformsTo R ε) :
    (∀ w ∈ tangentCone P.Ω xhat, 0 ≤ grad ⬝ᵥ w) ∧ -grad ∈ normalCone P.Ω xhat := by sorry

end GPSAnalysis.Core
