-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_display_4
-- name    : MTWalkSAT3CNF.TwoOcc.display_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:51.489847+00:00
-- url     : https://prove2.me/theorems/85fd57d5-fd43-4d00-abb0-1fbfc199009e
-- title:
--   §3.2 display (4) — flipping along an occurrence that is not an edge of the defect tree
-- statement:
--   Assume $\Delta(F)\le2$ and that every variable occurring twice has one positive and one negative occurrence. Let $\sigma$ be an assignment, $r$ an unsatisfied clause (the root of the defect tree $T$ containing it) and $p$ a position of $r$ whose occurrence is not an edge of $T$: a half-edge, or an edge to a clause of $A$. Put $W=W_T(r)$ and let $Q$ be the contribution to $\Phi$ of all other components before the update. If $\sigma'$ is $\sigma$ with the variable at $p$ flipped, then
--
--   $$\Phi(\sigma')\le Q+\frac14W+\frac12 .$$
--
--   Together with display (3), this gives the conditional drift $-1/4$ of the potential.
--
--   Differences from the source:
--   - encoding: Q, the contribution of all other components → Φ(σ) − W_T(r); reason: T is a defect tree rooted at r (Lemma 3.5) and contributes exactly W_T(r) to Φ
--   - encoding: an occurrence at r that is not an edge of T → every other occurrence of its variable lies in a clause of A (IsBoundary); reason: an other occurrence in a clause outside A would be adjacent to r and hence an edge of T
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), §3.2, display (4), p. 14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Potential

set_option autoImplicit false

namespace MTWalkSAT3CNF.TwoOcc

/-- §3.2 display (4), p. 14: in the opposite-sign case with `Δ(F) ≤ 2`, let `r` be an unsatisfied
clause (the root of the defect tree `T = K(r)`) and `p` a position of `r` whose occurrence is not
an edge of `T` (a half-edge, or an edge to a clause of `A`). With `W = W_T(r)` and
`Q = Φ(σ) − W` the contribution of all other components, flipping the variable at `p` gives
`Φ_{t+1} ≤ Q + W/4 + 1/2`. -/
theorem display_4 {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) (hopp : OppositeSign F) (σ : V → Bool) (r : Fin m)
    (hr : numTrue σ (F r) = 0) (p : Fin 3) (hp : IsBoundary F σ r p) :
    potential F (flip σ ((F r).var p)) ≤
      (potential F σ - compWeight F σ r) + compWeight F σ r / 4 + 1 / 2 := by sorry

end MTWalkSAT3CNF.TwoOcc
