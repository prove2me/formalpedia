-- Prove2me | Theorems.Thm_MSetBandit_pinv_estimate
-- name    : MSetBandit.pinv_estimate
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:44.315207+00:00
-- url     : https://prove2.me/theorems/5e454eaa-95a8-4d3e-a2dd-b64ea4239a1d
-- title:
--   [13, Cor. 1.2] (as invoked p.25) — pseudoinverse estimate $y^\top\Sigma^+y\le\sum_i y_i^2/(\mu_i(1-\mu_i))$
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Let $\theta\in\mathbb R^d$, $p=p_\theta$, $\mu=\mu(p)$ and $\Sigma=\Sigma(p)$. For every $y\in H_0$, i.e. $y^\top\mathbf 1=0$,
--   $$
--   y^\top\Sigma^+y\ \le\ \sum_{i=1}^d\frac{y_i^2}{\mu_i(1-\mu_i)},
--   $$
--   where $\Sigma^+$ is the Moore–Penrose pseudoinverse of $\Sigma$.
--
--   This is the pseudoinverse estimate of Cesari and Colomboni [13, Corollary 1.2] as the paper applies it in the proof of Lemma 1, where it turns the exact leverage-score identity of Lemma 2 into the affine majorant $\phi_p$.
--
--   Differences from the source:
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
--   - generalization: the page applies the estimate at $y=x-\mu$ for $p\in\mathcal P_\lambda$ (proof of Lemma 1); [13] is not restated in the paper → every $y\in H_0$ and every weighted $m$-set distribution $p_\theta$; reason: the estimate is cited as a property of the covariance on $H_0$; the page's use is the instance $y=x-\mu$
--   - encoding: $y\in H_0=\{y:y^\top\mathbf 1=0\}$ → $\sum_i y_i=0$; reason: definition of $H_0$, written out
--   - encoding: $\Sigma^+$, the Moore–Penrose pseudoinverse → the published operator pseudoinverse of $z\mapsto\Sigma z$ on Euclidean space; reason: Mathlib has no matrix pseudoinverse; same operator
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, proof of Lemma 1, p.25, citing [13, Corollary 1.2] (Cesari–Colomboni, arXiv:2607.13990v2)

import Mathlib
import Definitions.Def_MSetBandit_cov
import Definitions.Def_MSetBandit_wdist
import Definitions.Def_MSetBandit_pinvMat
open Matrix

namespace MSetBandit

/-- **The pseudoinverse estimate** ([13, Corollary 1.2] as invoked in Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, proof of Lemma 1,
p.25): "The pseudoinverse estimate in [13, Corollary 1.2] gives
`y^⊤Σ⁺y ≤ Σ_{i∈[d]} y_i² / (µ_i(1 − µ_i))`", for `y ∈ H₀`.

For `1 ≤ m ≤ d − 1`, every `θ ∈ ℝ^d`, `p = p_θ`, `µ = µ(p)`, `Σ = Σ(p)` and every `y` with
`y^⊤1 = 0`: `y^⊤ Σ⁺ y ≤ Σ_i y_i² / (µ_i(1 − µ_i))`.

**Formalization Note.** Proved in Cesari–Colomboni, arXiv:2607.13990v2 (reference [13]); stated as
the paper applies it, for every weighted m-set distribution. `Σ⁺` is the Moore–Penrose
pseudoinverse (`pinvMat`). -/
theorem pinv_estimate {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) (θ : Fin d → ℝ)
    (y : Fin d → ℝ) (hy : ∑ i, y i = 0) :
    y ⬝ᵥ pinvMat (cov (wdist (m := m) θ)) y ≤
      ∑ i, y i ^ 2 / (marg (wdist (m := m) θ) i * (1 - marg (wdist (m := m) θ) i)) := by sorry

end MSetBandit
