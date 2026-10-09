-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_proposition_4_2
-- name    : HighOrderWalks.OneSided.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:11.647728+00:00
-- url     : https://prove2.me/theorems/0af2a37c-c74d-4b3a-891d-2c361564eb8f
-- title:
--   Proposition 4.2, p. 11 — ⟨dφ, dψ⟩ = ⟨d*φ, d*ψ⟩ + ⟨φ, ψ⟩ + Σ_{τ∈X(k−1)} ⟨(M′)⁺_{τ,0}(I − M⁻_{τ,0})φ_τ, ψ_τ⟩
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex, $0\le k\le n-1$, and $\phi,\psi$ $k$-cochains. Then
--   $$\langle d\phi,d\psi\rangle=\langle d^*\phi,d^*\psi\rangle+\langle\phi,\psi\rangle+\sum_{\tau\in X(k-1)}\big\langle (M')^+_{\tau,0}(I-M^-_{\tau,0})\phi_\tau,\ \psi_\tau\big\rangle,$$
--   where for each $\tau\in X(k-1)$ the operators $(M')^+_{\tau,0}$ and $M^-_{\tau,0}$ are the non-lazy upper and the lower random walk on the vertices of the link $(X_\tau,m_\tau)$, and the inner product is that of $0$-cochains of $X_\tau$.
--
--   The last sum is the only term carrying spectral information about the links; bounding it is the content of Lemma 4.3.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 11, Proposition 4.2

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Proposition 4.2, p. 11: for `0 ≤ k ≤ n - 1` and `k`-cochains `φ, ψ`,
`⟨dφ, dψ⟩ = ⟨d*φ, d*ψ⟩ + ⟨φ, ψ⟩ + Σ_{τ ∈ X(k-1)} ⟨(M')⁺_{τ,0}(I - M⁻_{τ,0}) φ_τ, ψ_τ⟩`. -/
theorem proposition_4_2 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ ψ : Finset V → ℝ) :
    ip X m (k + 2) (dS X φ) (dS X ψ) =
      ip X m k (dStar X m φ) (dStar X m ψ) + ip X m (k + 1) φ ψ + linkTerm X m k φ ψ := by sorry

end HighOrderWalks.OneSided
