-- Prove2me | Theorems.Thm_KhintchineTwoRegime_lemma_5
-- name    : KhintchineTwoRegime.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:31.889211+00:00
-- url     : https://prove2.me/theorems/d32ba837-9cd7-4e2a-8637-4682c891275b
-- title:
--   Lemma 5 — $K_n(\omega)\ge\Phi_q(x)$ beyond $d_{\max}(4)$; $\Phi_q'(0)>0\iff q>2\sqrt2/3$; $\Phi_q''\le0$
-- statement:
--   Let $n\ge2$ and $\omega\in\mathcal C_n(\tau)$ with $\tau>d_{\max}(4)=\sqrt{2-\sqrt2}$. Put $q=\omega_1+\omega_2$ and $x=q-\omega_3-\omega_4$. Then $q<1$ and
--   $$
--   K_n(\omega)\ \ge\ \Phi_q(x)=\frac34q-\frac38x+\frac1{8\sqrt2}\Bigl(\sqrt{A_q(x)}+2\sqrt{B_q(x)}\Bigr),
--   $$
--   where $A_q(x)=1-q^2+qx$ and $B_q(x)=1-q^2+qx-x^2$. Moreover:
--
--   1. for every $q$ with $|q|<1$: $\Phi_q'(0)>0$ if and only if $q>2\sqrt2/3$;
--   2. for every $q$ and every $x$ with $A_q(x)>0$ and $B_q(x)>0$: $\Phi_q''(x)\le0$.
--
--   Lemma 5 reduces the minimization on $\mathcal C_n(\tau)$ to a one-variable concave function of $x$; Theorem 2 then shows $\Phi_q$ is increasing on the localized range of $x$.
--
--   **Formalization Note** Coordinates beyond $n$ are read as $0$; for $n\le4$ the set $\mathcal C_n(\tau)$ with $\tau>\sqrt{2-\sqrt2}$ is empty. Derivatives are Mathlib's `deriv`; at the stated points $\Phi_q$ is smooth, so they are the true derivatives.
--
--   Differences from the source:
--   - generalization: the derivative facts for Φ_q with q = ω₁ + ω₂ of the lemma (so 0 < q < 1) → clause (ii) for every q with |q| < 1, clause (iii) for every q; reason: the paper's q lies in (0, 1); the computation Φ_q′(0) = −3/8 + 3q/(16√2·√(1 − q²)) and the concavity argument hold on the larger ranges, which contain the paper's
--   - encoding: Φ″_q(x) ≤ 0 on every interval where A_q(x) and B_q(x) are positive → ∀ x, 0 < A_q(x) → 0 < B_q(x) → deriv (deriv Φ_q) x ≤ 0; reason: {x : A_q(x) > 0, B_q(x) > 0} is an open interval, so the pointwise and interval forms are the same statement
--   - encoding: x = q − ω₃ − ω₄ for ω ∈ C_n(τ) → coordinates read with pad (0 beyond n); reason: for n ≤ 4 and τ > √(2 − √2) the set C_n(τ) is empty, so the padding changes no instance
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 5, p.7

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_pad
import Definitions.Def_KhintchineTwoRegime_Phi

namespace KhintchineTwoRegime

/-- Lemma 5 (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), p.7): let `ω ∈ C_n(τ)` with `τ > d_max(4) = √(2 − √2)`; then `q < 1`
(`q = ω₁ + ω₂`), and `K_n(ω) ≥ Φ_q(x)` with `x = q − ω₃ − ω₄`. Moreover `Φ_q′(0) > 0` if
and only if `q > 2√2/3`, and `Φ_q″(x) ≤ 0` on every interval where `A_q(x)` and `B_q(x)` are
positive.

**Formalization Note** `n ≥ 2` is the standing assumption of §2 (p.4); coordinates are read
with `pad` (0 beyond `n`). For `n ≤ 4` the set `C_n(τ)` with `τ > √(2 − √2)` is empty.
The derivative clauses are stated for every `q` with `|q| < 1` (where `Φ_q` is
differentiable at `0`), resp. for every `q` and every `x` with `A_q(x), B_q(x) > 0` (the
set of such `x` is an open interval, on which `Φ_q` is smooth), via Mathlib's `deriv`. -/
theorem lemma_5 :
    (∀ n : ℕ, 2 ≤ n → ∀ τ : ℝ, ∀ ω ∈ Cn n τ, Real.sqrt (2 - Real.sqrt 2) < τ →
      pad ω 0 + pad ω 1 < 1 ∧
      Phi (pad ω 0 + pad ω 1) (pad ω 0 + pad ω 1 - pad ω 2 - pad ω 3) ≤ K n ω) ∧
    (∀ q : ℝ, |q| < 1 → (0 < deriv (Phi q) 0 ↔ 2 * Real.sqrt 2 / 3 < q)) ∧
    (∀ q x : ℝ, 0 < Aq q x → 0 < Bq q x → deriv (deriv (Phi q)) x ≤ 0) := by sorry

end KhintchineTwoRegime
