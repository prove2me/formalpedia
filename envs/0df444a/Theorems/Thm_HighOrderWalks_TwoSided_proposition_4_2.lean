-- Prove2me | Theorems.Thm_HighOrderWalks_TwoSided_proposition_4_2
-- name    : HighOrderWalks.TwoSided.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:54.804649+00:00
-- url     : https://prove2.me/theorems/7ba6739c-5bdd-437a-bf56-73c91af1b68c
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
import Definitions.Def_HighOrderWalks_TwoSided_Setting

namespace HighOrderWalks.TwoSided

/-- Proposition 4.2, p. 11: for `0 ≤ k ≤ n - 1` and `k`-cochains `φ, ψ`,
`⟨dφ, dψ⟩ = ⟨d*φ, d*ψ⟩ + ⟨φ, ψ⟩ + Σ_{τ ∈ X(k-1)} ⟨(M')⁺_{τ,0}(I - M⁻_{τ,0}) φ_τ, ψ_τ⟩`. -/
theorem proposition_4_2 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ ψ : Finset V → ℝ) :
    HighOrderWalks.OneSided.ip X m (k + 2) (HighOrderWalks.OneSided.dS X φ) (HighOrderWalks.OneSided.dS X ψ) =
      HighOrderWalks.OneSided.ip X m k (HighOrderWalks.OneSided.dStar X m φ) (HighOrderWalks.OneSided.dStar X m ψ) + HighOrderWalks.OneSided.ip X m (k + 1) φ ψ + HighOrderWalks.OneSided.linkTerm X m k φ ψ := by sorry

end HighOrderWalks.TwoSided
