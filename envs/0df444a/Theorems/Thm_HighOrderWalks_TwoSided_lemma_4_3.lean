-- Prove2me | Theorems.Thm_HighOrderWalks_TwoSided_lemma_4_3
-- name    : HighOrderWalks.TwoSided.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:42.153375+00:00
-- url     : https://prove2.me/theorems/568d85cf-57f6-488c-a172-1b204df29cf0
-- title:
--   Lemma 4.3 (second inequality), p. 12 — Σ_{τ∈X(k−1)} |⟨(M′)⁺_{τ,0}(I − M⁻_{τ,0})φ_τ, ψ_τ⟩| ≤ (k+1) max{μ_k, −ν_k}‖φ‖‖ψ‖
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex and $0\le k\le n-1$. For $\tau\in X(k-1)$ let $\mu_\tau$ and $\nu_\tau$ be the second largest and the smallest eigenvalue of the non-lazy upper random walk $(M')^+_{\tau,0}$ on the vertices of the link $(X_\tau,m_\tau)$, and $\mu_k=\max_{\tau\in X(k-1)}\mu_\tau$, $\nu_k=\min_{\tau\in X(k-1)}\nu_\tau$. Let $b\ge\max\{\mu_k,-\nu_k\}$. Then for all $k$-cochains $\phi,\psi$,
--   $$\sum_{\tau\in X(k-1)}\Big|\big\langle (M')^+_{\tau,0}(I-M^-_{\tau,0})\phi_\tau,\ \psi_\tau\big\rangle\Big|\le (k+1)\,b\,\|\phi\|\,\|\psi\| .$$
--
--   With $b=\max\{\mu_k,-\nu_k\}$ this is the printed inequality. Combined with Proposition 4.2 it controls the cross terms $\langle d\phi,d\psi\rangle$ by two-sided local spectral data, which is what Theorem 5.6 needs.
--
--   **Formalization Note.** The bound $\max\{\mu_k,-\nu_k\}\le b$ is the Rayleigh-quotient predicate `LinkTwoSided X m k b` of the definitions file. The absolute value is inside the sum, as printed. No sign hypothesis on $b$ is needed: by purity every link $X_\tau$, $\tau\in X(k-1)$, $k\le n-1$, has at least two vertices, so the predicate itself forces $b\ge0$.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 12, Lemma 4.3 (second inequality)

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting

namespace HighOrderWalks.TwoSided

/-- Lemma 4.3 (second inequality), p. 12: for `0 ≤ k ≤ n - 1` and `k`-cochains `φ, ψ`, if `b`
bounds `max{μ_k, -ν_k}` (for every `τ ∈ X(k-1)`, `|⟨(M')⁺_{τ,0} g, g⟩| ≤ b ‖g‖²` on the
`m_τ`-orthogonal complement of the constants), then
`Σ_{τ ∈ X(k-1)} |⟨(M')⁺_{τ,0}(I - M⁻_{τ,0}) φ_τ, ψ_τ⟩| ≤ (k+1) b ‖φ‖ ‖ψ‖`. -/
theorem lemma_4_3 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (b : ℝ) (hb : LinkTwoSided X m k b)
    (φ ψ : Finset V → ℝ) :
    ∑ τ ∈ HighOrderWalks.OneSided.cells X k, |HighOrderWalks.OneSided.linkSummand X m τ φ ψ| ≤
      ((k : ℝ) + 1) * b * HighOrderWalks.OneSided.nrm X m (k + 1) φ * HighOrderWalks.OneSided.nrm X m (k + 1) ψ := by sorry

end HighOrderWalks.TwoSided
