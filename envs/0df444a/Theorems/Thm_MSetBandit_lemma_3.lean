-- Prove2me | Theorems.Thm_MSetBandit_lemma_3
-- name    : MSetBandit.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:36.250575+00:00
-- url     : https://prove2.me/theorems/060067f7-4054-44cb-8bb0-6343ccd8d29c
-- title:
--   Lemma 3 — the surrogate loss satisfies $\eta|Z_t(x)|\le1/4$
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Suppose that $0<\eta\le1/64$ and $\lambda=128\eta d\le1/2$, that the loss vector $\ell\in\mathbb R^d$ of the round satisfies the action-normalized condition $|x^\top\ell|\le1$ for every $x\in\mathcal X$, and that $p=p_\theta$ is a weighted $m$-set distribution in $\mathcal P_{\lambda/2}$. Let $X_0\in\mathcal X$ be the drawn action, $Y=X_0^\top\ell$ the observed loss, $\hat\ell=M(p)^{-1}X_0Y$ the loss estimate, and $Z(x)=x^\top\hat\ell-\eta c_p^\top x$ the surrogate loss. Then
--   $$
--   \eta\,|Z(x)|\le\frac14\qquad\text{for every }x\in\mathcal X .
--   $$
--
--   This bound is what allows the second-order expansion of the exponential-weights potential in Lemma 4 and the KL control in Proposition 1.
--
--   Differences from the source:
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
--   - encoding: "Fix $t\in[T]$", the round-$t$ action $X_t$, loss $\ell_t$ and distribution $p_t$ → an arbitrary action $X_0$, loss vector $\ell$ and parameter $\theta$ satisfying the hypotheses; reason: the lemma is a deterministic statement about one round; the same instances
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix C, Lemma 3, p.26

import Mathlib
import Definitions.Def_MSetBandit_Plam
import Definitions.Def_MSetBandit_surrogate
open Matrix

namespace MSetBandit

/-- **Lemma 3** (Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix C, p.26). Fix a round. Suppose that `0 < η ≤ 1/64`,
`λ = 128ηd ≤ 1/2`, the loss `ℓ` of the round satisfies the action-normalized condition
`|x^⊤ℓ| ≤ 1` for all `x ∈ X`, and `p = p_θ` is a weighted m-set distribution in `P_{λ/2}`. Then,
for the drawn action `X₀`, the observed loss `Y = X₀^⊤ℓ`, the estimate `ℓ̂ = M(p)⁻¹X₀Y` and the
surrogate `Z(x) = x^⊤ℓ̂ − η c_p^⊤x`, we have `η|Z(x)| ≤ 1/4` for every `x ∈ X`.

**Formalization Note.** The statement is deterministic and holds for every action `X₀` (the
paper's `X_t`); `1 ≤ m ≤ d − 1` is the paper's standing assumption. -/
theorem lemma_3 {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) {η lam : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 64) (hlam : lam = 128 * η * d) (hlam2 : lam ≤ 1 / 2) (ℓ : Fin d → ℝ)
    (hℓ : ∀ x : Action d m, |ind x ⬝ᵥ ℓ| ≤ 1) (θ : Fin d → ℝ)
    (hp : wdist (m := m) θ ∈ Plam (lam / 2)) (X₀ : Action d m) :
    ∀ x : Action d m, η * |surrogate η θ X₀ (ind X₀ ⬝ᵥ ℓ) x| ≤ 1 / 4 := by sorry

end MSetBandit
