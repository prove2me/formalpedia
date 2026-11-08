-- Prove2me | Theorems.Thm_MSetBandit_eq_51
-- name    : MSetBandit.eq_51
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T00:43:33.679213+00:00
-- url     : https://prove2.me/theorems/b42748c5-1c5d-4885-9508-f1bad3d46d34
-- title:
--   Eq. (51) — the estimated loss is unbiased under $p_t$: $\mathbb E_{X\sim p_t}[\hat y_t(X)]=Y_t$
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Let $\theta\in\mathbb R^d$, $p=p_\theta$, $M=M(p)$, let $X_0\in\mathcal X$ be any action and $Y\in\mathbb R$ any real number, and let $\hat y(x)=x^\top\hat\ell$ with $\hat\ell=M^{-1}X_0Y$. Then
--   $$
--   \mathbb E_{X\sim p}[\hat y(X)]=\mu(p)^\top M^{-1}X_0\,Y=Y .
--   $$
--
--   In the proof of Theorem 1 this is applied at every round with $p=p_t$, the drawn action $X_t$ and the observed loss $Y_t$: the learner's average estimated loss equals its realized loss.
--
--   Differences from the source:
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
--   - generalization: the round-$t$ quantities $p_t$, $X_t$, $Y_t$ of a run of Algorithm 1 → every weighted $m$-set distribution $p_\theta$, every action $X_0$ and every real $Y$; reason: the identity uses only that $p_t$ is a weighted $m$-set distribution; it specializes to every round
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix C.1, proof of Theorem 1, Eq. (51), p.31

import Mathlib
import Definitions.Def_MSetBandit_lossEst
import Definitions.Def_MSetBandit_expect
open Matrix

namespace MSetBandit

/-- **The estimated loss is unbiased under `p_t`, Eq. (51)** (Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix C.1, proof of
Theorem 1, p.31): "`1^⊤X = m` for every `X ∈ X`, so `M_t1 = E_{X∼p_t}[X(X^⊤1)] = mµ_t`. Since
`M_t` is symmetric and invertible, this gives `E_{X∼p_t}[ŷ_t(X)] = µ_t^⊤M_t⁻¹X_tY_t = 1^⊤X_t Y_t/m
= Y_t`" (51).

For `1 ≤ m ≤ d − 1`, every `θ`, every action `X₀` and every real `Y`, with `ŷ(x) = x^⊤ℓ̂`,
`ℓ̂ = M(p_θ)⁻¹X₀Y`: `E_{X∼p_θ}[ŷ(X)] = Y`.

**Formalization Note.** Stated for every weighted m-set distribution, every action and every
observed loss (the identity is deterministic). -/
theorem eq_51 {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) (θ : Fin d → ℝ) (X₀ : Action d m)
    (Y : ℝ) :
    expect (wdist θ) (fun x : Action d m => ind x ⬝ᵥ lossEst θ X₀ Y) = Y := by sorry

end MSetBandit
