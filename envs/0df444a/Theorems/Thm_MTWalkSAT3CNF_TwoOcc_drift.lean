-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_drift
-- name    : MTWalkSAT3CNF.TwoOcc.drift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:52.334196+00:00
-- url     : https://prove2.me/theorems/e384fbe2-bf7c-4375-8a3b-af512ddce457
-- title:
--   §3.2 — the conditional drift of $\Phi$ is at most $-1/4$
-- statement:
--   Assume $\Delta(F)\le2$ and that every variable occurring twice has one positive and one negative occurrence. Let $\sigma$ be an assignment and $r$ an unsatisfied clause, the clause the rule selects at the current step. If a position $p$ of $r$ is chosen with probability $1/3$ each and its variable is flipped, the expected next potential satisfies
--
--   $$\frac13\sum_{p=1}^{3}\Phi\bigl(\sigma\text{ with }\mathrm{var}(r,p)\text{ flipped}\bigr)\le\Phi(\sigma)-\frac14 .$$
--
--   Since every adaptive rule selects some unsatisfied clause, this is the bound $\mathbb E[\Phi_{t+1}\mid\mathcal F_t]\le\Phi_t-\frac14$ used to telescope to $\mathbb E[T_{WS}]\le 4m$.
--
--   Differences from the source:
--   - encoding: conditional on the history and on the rule selecting r, E[Φ_{t+1} | F_t] ≤ Φ_t − 1/4 → the deterministic average (1/3) Σ_p Φ(σ with var(r,p) flipped) ≤ Φ(σ) − 1/4 for every assignment σ and unsatisfied clause r; reason: given the history and the selected clause r, the next state is σ flipped at a uniformly chosen position of r, so the conditional expectation is exactly this average
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), §3.2, p. 16 (conditional drift at most −1/4). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Potential

set_option autoImplicit false

namespace MTWalkSAT3CNF.TwoOcc

/-- §3.2, p. 16, the conditional drift: in the opposite-sign case with `Δ(F) ≤ 2`, when the rule
selects an unsatisfied clause `r` and a position of `r` is chosen with probability `1/3` each,
the expected potential after the flip is at most `Φ(σ) − 1/4`. -/
theorem drift {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) (hopp : OppositeSign F) (σ : V → Bool) (r : Fin m)
    (hr : numTrue σ (F r) = 0) :
    (1 / 3 : ℝ) * ∑ p : Fin 3, potential F (flip σ ((F r).var p)) ≤
      potential F σ - 1 / 4 := by sorry

end MTWalkSAT3CNF.TwoOcc
