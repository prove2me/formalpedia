-- Prove2me | Theorems.Thm_MSetBandit_cov_ker_eq_span_one
-- name    : MSetBandit.cov_ker_eq_span_one
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:40.361666+00:00
-- url     : https://prove2.me/theorems/7531333a-9502-4ba0-8978-d3cf376ebd2a
-- title:
--   [13, Cor. 1.2] (as invoked p.24) — $\ker\Sigma=\mathrm{span}\{\mathbf 1\}$ and $\mathrm{range}\,\Sigma=H_0$ for weighted $m$-set distributions
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Let $\theta\in\mathbb R^d$ and let $\Sigma=\Sigma(p_\theta)$ be the covariance matrix of the weighted $m$-set distribution $p_\theta$. Then
--   1. the kernel of $\Sigma$ is the line of constant vectors: $\Sigma z=\mathbf 0$ if and only if $z=a\mathbf 1$ for some $a\in\mathbb R$;
--   2. the range of $\Sigma$ is the hyperplane $H_0=\{y\in\mathbb R^d:\ y^\top\mathbf 1=0\}$: a vector $y$ equals $\Sigma z$ for some $z$ if and only if $y^\top\mathbf 1=0$.
--
--   $$
--   \ker\Sigma(p_\theta)=\operatorname{span}\{\mathbf 1\},\qquad \operatorname{range}\Sigma(p_\theta)=H_0 .
--   $$
--
--   This is the covariance structure of conditional Bernoulli distributions from Cesari and Colomboni [13, Corollary 1.2], as the paper invokes it in the proof of Lemma 2; it identifies on which vectors the covariance pseudoinverse acts as an inverse.
--
--   Differences from the source:
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
--   - encoding: $y\in H_0=\{y:y^\top\mathbf 1=0\}$ → $\sum_i y_i=0$; reason: definition of $H_0$, written out
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, proof of Lemma 2, p.24, citing [13, Corollary 1.2] (Cesari–Colomboni, arXiv:2607.13990v2)

import Mathlib
import Definitions.Def_MSetBandit_cov
import Definitions.Def_MSetBandit_wdist
open Matrix

namespace MSetBandit

/-- **Kernel and range of the covariance of a weighted m-set distribution** ([13, Corollary 1.2]
as invoked in Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, proof of Lemma 2, p.24): "By [13, Corollary 1.2], `ker(Σ) = span{1}`. Since
`Σ` is symmetric, its range satisfies `range(Σ) = ker(Σ)^⊥ = H₀`."

For `1 ≤ m ≤ d − 1`, every `θ ∈ ℝ^d` and `Σ = Σ(p_θ)`:
1. `Σz = 0` if and only if `z` is a constant vector `a·1`;
2. `y = Σz` for some `z` if and only if `y^⊤1 = 0`.

**Formalization Note.** The result is proved in Cesari–Colomboni, arXiv:2607.13990v2 (reference
[13]); it is stated here as the paper applies it, for every weighted m-set distribution. `H₀` is
written `Σ_i y_i = 0`. -/
theorem cov_ker_eq_span_one {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) (θ : Fin d → ℝ) :
    (∀ z : Fin d → ℝ, cov (wdist (m := m) θ) *ᵥ z = 0 ↔ ∃ a : ℝ, z = fun _ => a) ∧
    (∀ y : Fin d → ℝ, (∃ z, cov (wdist (m := m) θ) *ᵥ z = y) ↔ ∑ i, y i = 0) := by sorry

end MSetBandit
