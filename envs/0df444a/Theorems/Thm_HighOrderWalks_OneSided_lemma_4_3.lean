-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_lemma_4_3
-- name    : HighOrderWalks.OneSided.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:38.45556+00:00
-- url     : https://prove2.me/theorems/6d34e633-2ab7-4afd-aad3-405f54aa8968
-- title:
--   Lemma 4.3 (first inequality), p. 12 — Σ_{τ∈X(k−1)} ⟨(M′)⁺_{τ,0}(I − M⁻_{τ,0})φ_τ, φ_τ⟩ ≤ (k+1)μ‖φ‖² for μ ≥ max(μ_k, 0)
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex and $0\le k\le n-1$. Let $\mu\ge0$ be such that for every $\tau\in X(k-1)$ the second largest eigenvalue $\mu_\tau$ of the non-lazy upper walk $(M')^+_{\tau,0}$ on the link $X_\tau$ is at most $\mu$ (that is, $\mu\ge\max(\mu_k,0)$). Then for every $k$-cochain $\phi$,
--   $$\sum_{\tau\in X(k-1)}\big\langle (M')^+_{\tau,0}(I-M^-_{\tau,0})\phi_\tau,\ \phi_\tau\big\rangle\le (k+1)\,\mu\,\|\phi\|^2 .$$
--
--   Combined with Proposition 4.2, this bounds $\|d\phi\|^2$ by local spectral data.
--
--   **Formalization Note.** The page states the bound with $\mu=\mu_k$. As printed it fails when $\mu_k<0$: for $k=0$, the complete graph on $N\ge3$ vertices with unit edge weights ($\mu_0=-1/(N-1)$) and $\phi\equiv1$, the left side is $0$ and the right side is negative. The proof's step $\mu_k\|(I-M^-)\phi_\tau\|^2\le\mu_k\|\phi_\tau\|^2$ needs $\mu_k\ge0$; the hypothesis $0\le\mu$ is added for that reason, and the statement is the printed one with $\mu_k$ replaced by $\max(\mu_k,0)$. The eigenvalue bound $\mu_\tau\le\mu$ is the Rayleigh-quotient predicate `LinkUpper` of the definitions file.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 12, Lemma 4.3 (first inequality)

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Lemma 4.3 (first inequality), p. 12, with the correction `0 ≤ μ`: for `0 ≤ k ≤ n - 1`, if
`μ ≥ 0` bounds the second largest eigenvalue of `(M')⁺_{τ,0}` for every `τ ∈ X(k-1)`, then
`Σ_{τ ∈ X(k-1)} ⟨(M')⁺_{τ,0}(I - M⁻_{τ,0}) φ_τ, φ_τ⟩ ≤ (k+1) μ ‖φ‖²`. -/
theorem lemma_4_3 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ : LinkUpper X m k μ)
    (φ : Finset V → ℝ) :
    linkTerm X m k φ φ ≤ ((k : ℝ) + 1) * μ * ip X m (k + 1) φ φ := by sorry

end HighOrderWalks.OneSided
