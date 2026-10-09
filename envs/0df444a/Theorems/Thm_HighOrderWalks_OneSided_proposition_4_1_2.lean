-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_proposition_4_1_2
-- name    : HighOrderWalks.OneSided.proposition_4_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:02.117105+00:00
-- url     : https://prove2.me/theorems/da68b54b-1ab9-4404-88b4-c5edf28aaec6
-- title:
--   Proposition 4.1 (2), p. 10 — binom(l, k+1)⟨d*φ, d*ψ⟩ = Σ_{τ∈X(k)} ⟨d*_τφ_τ, d*_τψ_τ⟩
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex, let $-1\le k<l\le n$, and let $\phi,\psi$ be $l$-cochains. Write $d^*$ for the adjoint signless differential of $X$ and $d^*_\tau$ for that of the link $(X_\tau,m_\tau)$. Then
--   $$\binom{l}{k+1}\langle d^*\phi,d^*\psi\rangle=\sum_{\tau\in X(k)}\langle d^*_\tau\phi_\tau,d^*_\tau\psi_\tau\rangle .$$
--
--   This is the localization identity for $d^*$.
--
--   **Formalization Note.** With $c=k+1$, the hypotheses are $c\le l\le n$. $d^*\phi$ lives on faces of $X$ with $l$ vertices and $d^*_\tau\phi_\tau$ on faces of $X_\tau$ with $l-c$ vertices (natural subtraction, exact since $c\le l$).
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 10, Proposition 4.1 (2) (proof in Appendix A, pp. 28–29)

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Proposition 4.1 (2), p. 10: for `-1 ≤ k < l ≤ n` (`c = k + 1 ≤ l`) and `l`-cochains
`φ, ψ`, `binom(l, k+1) ⟨d*φ, d*ψ⟩ = Σ_{τ ∈ X(k)} ⟨d*_τ φ_τ, d*_τ ψ_τ⟩`, where `d*_τ` is the
adjoint differential of the link `X_τ` with weight `m_τ`. -/
theorem proposition_4_1_2 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (c l : ℕ) (hcl : c ≤ l) (hl : l ≤ n) (φ ψ : Finset V → ℝ) :
    (Nat.choose l c : ℝ) * ip X m l (dStar X m φ) (dStar X m ψ) =
      ∑ τ ∈ cells X c, ip (link X τ) (linkWeight m τ) (l - c)
        (dStar (link X τ) (linkWeight m τ) (loc φ τ))
        (dStar (link X τ) (linkWeight m τ) (loc ψ τ)) := by sorry

end HighOrderWalks.OneSided
