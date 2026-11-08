-- Prove2me | Theorems.Thm_KhintchineTwoRegime_lemma_2
-- name    : KhintchineTwoRegime.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:38.405206+00:00
-- url     : https://prove2.me/theorems/9ff13281-f0ba-4282-9626-fcbfacb81e3d
-- title:
--   Lemma 2 — coefficient bounds $K_n(\omega)\ge a$, $\ge J(a,b)$, $\ge H(a,b)$
-- statement:
--   Let $\omega\in\mathbb R^n$ be a proper unit vector and put $a=\omega_1$, $b=\omega_2$ (with $\omega_2=0$ if $n=1$). Then
--   $$
--   K_n(\omega)\ge a,\tag{11}
--   $$
--   $$
--   K_n(\omega)\ge J(a,b)=\frac{a+b}2+\frac{\sqrt{1-2ab}}{2\sqrt2},\tag{12}
--   $$
--   $$
--   K_n(\omega)\ge H(a,b)=C\bigl[a^2r(a)+(1-a^2)r(b)\bigr].\tag{13}
--   $$
--   These three coefficient-dependent bounds feed the scalar separation of Corollary 1.
--
--   Differences from the source:
--   - encoding: put a = ω₁ and b = ω₂, adding a zero coordinate if necessary → a = pad ω 0, b = pad ω 1 (0 beyond the last coordinate); reason: the padded coordinate is exactly the adjoined zero; same instances
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 2, eqs. (11)–(13), p.6

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_IsProper
import Definitions.Def_KhintchineTwoRegime_pad
import Definitions.Def_KhintchineTwoRegime_J
import Definitions.Def_KhintchineTwoRegime_H

namespace KhintchineTwoRegime

/-- Lemma 2 (Coefficient-dependent bounds) (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eqs. (11)–(13), p.6): for a proper unit
vector `ω` with `a = ω₁`, `b = ω₂` (adding a zero coordinate if necessary),
`K_n(ω) ≥ a`, `K_n(ω) ≥ J(a, b)` and `K_n(ω) ≥ H(a, b)`.

**Formalization Note** `a = pad ω 0`, `b = pad ω 1`: the coordinate beyond the last one is
`0`, which is the paper's "adding a zero coordinate". -/
theorem lemma_2 (n : ℕ) (ω : Fin n → ℝ) (hω : IsProper ω) :
    pad ω 0 ≤ K n ω ∧ J (pad ω 0) (pad ω 1) ≤ K n ω ∧ H (pad ω 0) (pad ω 1) ≤ K n ω := by sorry

end KhintchineTwoRegime
