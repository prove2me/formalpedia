-- Prove2me | Theorems.Thm_MaskingHardness_theorem_1_9_radius
-- name    : MaskingHardness.theorem_1_9_radius
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:06.383867+00:00
-- url     : https://prove2.me/theorems/eaeb0a98-ead7-4830-8bc6-49f3d10125fe
-- title:
--   Proof of Theorem 1.9, p.23 — when $\varepsilon>0$, $\lambda$ with $\|\lambda\|_1>r=(\mathbb E[g(y,0)]-v)/\varepsilon$ is beaten by $\lambda=0$
-- statement:
--   Let $\mathcal D$ be a distribution over $\mathcal X\times[k]$, $\mathcal C=\{c_i\}$ a finite collection, $g:[k]\times\mathbb R^k\to\mathbb R$, and $\varepsilon>0$. Suppose $g$ is bounded below by $v\in\mathbb R$ on centered actions: $g(y,\pi(a))\ge v$ for all $y$ and $a$. Put
--
--   $$
--   r=\frac{\mathbb E[g(y,0)]-v}{\varepsilon}.
--   $$
--
--   Then every $\lambda$ with $\|\lambda\|_1>r$ is strictly outperformed by $\lambda=0$:
--
--   $$
--   \mathbb E\bigl[g(y,\pi(c_0(x)))\bigr]+\varepsilon\|0\|_1<\mathbb E\bigl[g(y,\pi(c_\lambda(x)))\bigr]+\varepsilon\|\lambda\|_1 .
--   $$
--
--   This confines the minimization of the main theorem to a compact $\ell_1$ ball, which yields the attainment clause of Theorem 1.9.
--
--   **Formalization Note** Both sides are values of the regularized loss $L(\lambda)$; $\|\lambda\|_1=\sum_i|\lambda_i|$.
--
--   Differences from the source:
--   - generalization: g, h convex–concave conjugates (the setting of Theorem 1.9) → any real-valued g, no conjugacy hypothesis; reason: the step uses only the lower bound v; conjugate pairs are a special case
--   - generalization: a finite set C ⊆ {X → ℝᵏ} → a finite indexed family c : ι → X → ℝᵏ, repetitions allowed; reason: the paper's set C is the family indexed by its own elements (ι = C, c = inclusion), so the statement specializes to the source's
--   - encoding: a distribution D over X × Y → weights D x y ≥ 0 summing to 1 (IsDist); expectations are the weighted finite sums; reason: finite sets; same distributions, zero-probability pairs allowed
--   - encoding: ‖λ‖₁ → ∑ i, |λ i|; reason: Mathlib's norm on ι → ℝ is the sup norm; this is the ℓ₁ norm
--   - encoding: g bounded below by v ∈ ℝ on centered actions → ∀ y a, v ≤ g y (centered a); reason: same condition
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), proof of Theorem 1.9, second part, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_centered
import Definitions.Def_MaskingHardness_lossObjective

namespace MaskingHardness

/-- **Proof of Theorem 1.9, second part: the radius `r`** (Gopalan–Prabhakaran–Tankala,
*Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d,
proof of Theorem 1.9, printed p.23 = PDF p.25).

Suppose `g` is bounded below by `v ∈ ℝ` on centered actions and `ε > 0`. Then every `λ` with
`‖λ‖₁ > r = (E[g(y, 0)] − v)/ε` is strictly outperformed by `λ = 0`:
`E[g(y, π(c_0(x)))] + ε‖0‖₁ < E[g(y, π(c_λ(x)))] + ε‖λ‖₁`.

**Formalization Note** "bounded below on centered actions" is `∀ y a, v ≤ g y (π a)`;
`‖λ‖₁ = ∑ᵢ |λᵢ|`; no conjugacy hypothesis is needed for this step. -/
theorem theorem_1_9_radius {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ)
    (g : Fin k → (Fin k → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (v : ℝ) (hv : ∀ y a, v ≤ g y (centered a)) (lam : ι → ℝ)
    (hlam : (∑ x, ∑ y, D x y * g y 0 - v) / ε < ∑ i, |lam i|) :
    lossObjective D c g ε 0 < lossObjective D c g ε lam := by sorry

end MaskingHardness
