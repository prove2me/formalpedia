-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_proposition_4_1_3
-- name    : HighOrderWalks.OneSided.proposition_4_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:18.556933+00:00
-- url     : https://prove2.me/theorems/95025fae-e1c0-423a-a143-1ddb35ed8737
-- title:
--   Proposition 4.1 (3), p. 10 — ⟨dφ, dψ⟩ = Σ_{τ∈X(l−1)} (⟨d_τφ_τ, d_τψ_τ⟩ − (l/(l+1))⟨φ_τ, ψ_τ⟩)
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex, let $0\le l<n$, and let $\phi,\psi$ be $l$-cochains. For $\tau\in X(l-1)$, the localizations $\phi_\tau,\psi_\tau$ are $0$-cochains of the link $X_\tau$, and $d_\tau$ is the signless differential of $X_\tau$. Then
--   $$\langle d\phi,d\psi\rangle=\sum_{\tau\in X(l-1)}\Big(\langle d_\tau\phi_\tau,d_\tau\psi_\tau\rangle-\frac{l}{l+1}\langle\phi_\tau,\psi_\tau\rangle\Big).$$
--
--   This is the localization identity for $d$; together with parts (1) and (2) it is what turns spectral information about links into global information.
--
--   **Formalization Note.** $d\phi$ lives on faces with $l+2$ vertices; $\tau$ ranges over faces with $l$ vertices; the link inner products are on link faces with $2$ and $1$ vertices.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 10, Proposition 4.1 (3) (proof in Appendix A, pp. 28–29)

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Proposition 4.1 (3), p. 10: for `l < n` and `l`-cochains `φ, ψ`,
`⟨dφ, dψ⟩ = Σ_{τ ∈ X(l-1)} (⟨d_τ φ_τ, d_τ ψ_τ⟩ - (l/(l+1)) ⟨φ_τ, ψ_τ⟩)`, the link inner products
being on `1`-cochains and `0`-cochains of `X_τ` (faces with `2` and `1` vertices). -/
theorem proposition_4_1_3 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (l : ℕ) (hl : l < n) (φ ψ : Finset V → ℝ) :
    ip X m (l + 2) (dS X φ) (dS X ψ) =
      ∑ τ ∈ cells X l,
        (ip (link X τ) (linkWeight m τ) 2 (dS (link X τ) (loc φ τ)) (dS (link X τ) (loc ψ τ)) -
          (l : ℝ) / ((l : ℝ) + 1) * ip (link X τ) (linkWeight m τ) 1 (loc φ τ) (loc ψ τ)) := by sorry

end HighOrderWalks.OneSided
