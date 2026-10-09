-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_lemma_C_4
-- name    : LinearMDPRL.Misspec.lemma_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:28.578986+00:00
-- url     : https://prove2.me/theorems/13aeaec6-0b16-4f79-81ba-078d7deb6332
-- title:
--   Lemma C.4, p. 22 — |φ^⊤(Λ^k_h)^{-1}Σ_{τ<k}φ^τ_h ε_τ| ≤ B√(dk φ^⊤(Λ^k_h)^{-1}φ) for |ε_τ| ≤ B
-- statement:
--   Let $\lambda>0$, let $(x^\tau_h,a^\tau_h)$ be arbitrary data with features $\phi^\tau_h=\phi(x^\tau_h,a^\tau_h)$, and let $\Lambda^k_h=\sum_{\tau=1}^{k-1}\phi^\tau_h(\phi^\tau_h)^\top+\lambda I$. Let $\{\varepsilon_\tau\}$ be any real sequence with $|\varepsilon_\tau|\le B$ for every $\tau$. Then for any $(h,k)\in[H]\times[K]$ and any $\phi\in\mathbb R^d$,
--   $$\Big|\phi^\top(\Lambda^k_h)^{-1}\sum_{\tau=1}^{k-1}\phi^\tau_h\varepsilon_\tau\Big|\le B\sqrt{dk\,\phi^\top(\Lambda^k_h)^{-1}\phi}.$$
--
--   This controls the error that model misspecification injects into the least-squares weights; unlike the stochastic noise of Lemma C.3, the $\varepsilon_\tau$ can be adversarial.
--
--   **Formalization Note** The data and $\lambda>0$ are arbitrary; in the proof of Theorem 3.2 the lemma is used with $\lambda=1$ and $B=2H\zeta$.
-- source:
--   arXiv:1907.05388v2, Lemma C.4, p. 22

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB

open Matrix

namespace LinearMDPRL.Misspec

universe u v

/-- **Lemma C.4** (p. 22). Let `{ε_τ}` be any sequence with `|ε_τ| ≤ B` for every `τ`. Then for any
`(h, k) ∈ [H] × [K]` and any `φ ∈ ℝ^d`,
`|φ^⊤ (Λ^k_h)^{-1} Σ_{τ=1}^{k-1} φ^τ_h ε_τ| ≤ B √(d k φ^⊤ (Λ^k_h)^{-1} φ)`,
where `Λ^k_h = Σ_{τ=1}^{k-1} φ^τ_h (φ^τ_h)^⊤ + λI` is built from arbitrary data. -/
theorem lemma_C_4 {S : Type u} {A : Type v} (d H K : ℕ) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (lam : ℝ) (hlam : 0 < lam) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (B : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ τ, |ε τ| ≤ B) :
    ∀ h ∈ Finset.Icc 1 H, ∀ k ∈ Finset.Icc 1 K, ∀ v : Fin d → ℝ,
      |v ⬝ᵥ (LinearMDPRL.Linear.gram φ lam xs as k h)⁻¹ *ᵥ
          ∑ τ ∈ Finset.Ico 1 k, ε τ • WithLp.ofLp (φ (xs τ h) (as τ h))|
        ≤ B * Real.sqrt (d * k * (v ⬝ᵥ (LinearMDPRL.Linear.gram φ lam xs as k h)⁻¹ *ᵥ v)) := by sorry

end LinearMDPRL.Misspec
