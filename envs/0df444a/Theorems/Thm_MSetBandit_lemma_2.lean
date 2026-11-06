-- Prove2me | Theorems.Thm_MSetBandit_lemma_2
-- name    : MSetBandit.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:50.32151+00:00
-- url     : https://prove2.me/theorems/207c906b-d100-4784-965d-110c17febae6
-- title:
--   Lemma 2 — $M\succ0$ and $x^\top M^{-1}x=1+(x-\mu)^\top\Sigma^+(x-\mu)$
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Let $p=p_\theta$ be a weighted $m$-set distribution, with marginal vector $\mu=\mu(p)$, second-moment matrix $M=M(p)$ and covariance matrix $\Sigma=\Sigma(p)$. Then
--   1. $M$ is positive definite;
--   2. for every $y\in H_0$ (that is, $y^\top\mathbf 1=0$), $\;y^\top M^{-1}y=y^\top\Sigma^+y$;
--   3. consequently, for every action $x\in\mathcal X$,
--   $$
--   x^\top M^{-1}x=1+(x-\mu)^\top\Sigma^+(x-\mu).
--   $$
--
--   The identity relates the leverage score of an action to the covariance pseudoinverse; combined with the pseudoinverse estimate it gives Lemma 1.
--
--   Differences from the source:
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
--   - encoding: $y\in H_0=\{y:y^\top\mathbf 1=0\}$ → $\sum_i y_i=0$; reason: definition of $H_0$, written out
--   - encoding: $\Sigma^+$, the Moore–Penrose pseudoinverse → the published operator pseudoinverse of $z\mapsto\Sigma z$ on Euclidean space; reason: Mathlib has no matrix pseudoinverse; same operator
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix B, Lemma 2, p.24

import Mathlib
import Definitions.Def_MSetBandit_cov
import Definitions.Def_MSetBandit_wdist
import Definitions.Def_MSetBandit_pinvMat
open Matrix

namespace MSetBandit

/-- **Lemma 2** (Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix B, p.24). Let `p ∈ ∆(X)` be a weighted m-set distribution, where
`1 ≤ m ≤ d − 1`. Then its second-moment matrix `M` is positive definite and, for every `y ∈ H₀`,
`y^⊤M⁻¹y = y^⊤Σ⁺y`. Consequently, for every `x ∈ X`, `x^⊤M⁻¹x = 1 + (x − µ)^⊤Σ⁺(x − µ)`, where
`µ = µ(p)` and `Σ = Σ(p)`.

**Formalization Note.** `p = p_θ` for an arbitrary `θ`; `H₀ = {y : Σ_i y_i = 0}`; `M⁻¹` is the
matrix inverse and `Σ⁺` the Moore–Penrose pseudoinverse (`pinvMat`). -/
theorem lemma_2 {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) (θ : Fin d → ℝ) :
    (secondMoment (wdist (m := m) θ)).PosDef ∧
    (∀ y : Fin d → ℝ, ∑ i, y i = 0 →
      y ⬝ᵥ ((secondMoment (wdist (m := m) θ))⁻¹ *ᵥ y) = y ⬝ᵥ pinvMat (cov (wdist (m := m) θ)) y) ∧
    (∀ x : Action d m,
      ind x ⬝ᵥ ((secondMoment (wdist (m := m) θ))⁻¹ *ᵥ ind x) =
        1 + (ind x - marg (wdist (m := m) θ)) ⬝ᵥ
          pinvMat (cov (wdist (m := m) θ)) (ind x - marg (wdist (m := m) θ))) := by sorry

end MSetBandit
