-- Prove2me | Theorems.Thm_KAdaptability_EpsApprox_lemma_1
-- name    : KAdaptability.EpsApprox.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:00:34.708679+00:00
-- url     : https://prove2.me/theorems/f01876b2-b26b-47fa-b5c5-cff74482c7e8
-- title:
--   Lemma 1 — Ξ_ε(ℓ) converges to Ξ(ℓ) in Hausdorff distance as ε ↓ 0
-- statement:
--   Fix a decision $(x,\{y^k\}_{k\in\mathcal K})\in\mathcal X\times\mathcal Y^K$ and $\ell\in\mathcal L=\{0,\dots,L\}^K$, and assume $\Xi(\ell)\ne\emptyset$, where $\Xi(\ell)$ and $\Xi_\varepsilon(\ell)$ are the exact and the approximate uncertainty sets of problems (6) and $(6_\varepsilon)$, and $\Xi$ is a nonempty bounded polyhedron. Then
--   $$\lim_{\varepsilon\downarrow0} d^{\mathrm H}\big(\Xi_\varepsilon(\ell),\Xi(\ell)\big)=0,$$
--   where the Hausdorff distance of two sets $X,Y\subseteq\mathbb R^Q$ is
--   $$d^{\mathrm H}(X,Y)=\max\Big\{\sup_{x\in X}\inf_{y\in Y}\|x-y\|,\ \sup_{y\in Y}\inf_{x\in X}\|x-y\|\Big\}$$
--   with the Euclidean norm.
--
--   The sets $\Xi(\ell)$ are in general not closed; the lemma says that the closed inner approximations $\Xi_\varepsilon(\ell)$ exhaust them, and it is the ingredient that turns closeness of the uncertainty sets into closeness of the objective values in Proposition 2.
--
--   **Formalization Note** The distance is Mathlib's extended Hausdorff distance `Metric.hausdorffEDist` on `EuclideanSpace ℝ (Fin nQ)`, valued in $[0,+\infty]$, and the limit is taken along `𝓝[>] 0`. The extended distance between a nonempty and an empty set is $+\infty$, so the statement contains the fact that $\Xi_\varepsilon(\ell)\ne\emptyset$ for small $\varepsilon$ (the real-valued `Metric.hausdorffDist` would be $0$ there and lose it).
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec6 (PDF p. 40), Lemma 1

import Mathlib
import Definitions.Def_KAdaptability_EpsApprox_Approx

namespace KAdaptability.EpsApprox

open Problem Filter Topology

/-- **Lemma 1** (p. ec6). Fix a decision `(x, {y^k}_{k∈𝒦}) ∈ 𝒳 × 𝒴^K` and `ℓ ∈ ℒ` with
`Ξ(ℓ) ≠ ∅`. Then `Ξ_ε(ℓ)` converges to `Ξ(ℓ)` in Hausdorff distance (Euclidean norm) as `ε ↓ 0`:
`lim_{ε↓0} d_H(Ξ_ε(ℓ), Ξ(ℓ)) = 0`. The extended Hausdorff distance is `+∞` when exactly one of
the two sets is empty, so the statement includes `Ξ_ε(ℓ) ≠ ∅` for small `ε`. -/
theorem lemma_1 {N M L nQ R K : ℕ} (P : Problem N M L nQ R)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : P.IsDecision x y)
    (ℓ : Fin K → Fin (L + 1)) (hne : (P.XiL x y ℓ).Nonempty) :
    Tendsto (fun ε : ℝ => Metric.hausdorffEDist (P.XiEps ε x y ℓ) (P.XiL x y ℓ))
      (𝓝[>] 0) (𝓝 0) := by sorry

end KAdaptability.EpsApprox
