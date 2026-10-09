-- Prove2me | Theorems.Thm_HighOrderWalks_TwoSided_proposition_4_1_1
-- name    : HighOrderWalks.TwoSided.proposition_4_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:58.715494+00:00
-- url     : https://prove2.me/theorems/5e34f951-43df-468b-adc9-76e6ba39f13d
-- title:
--   Proposition 4.1 (1), p. 10 — binom(l+1, k+1)⟨φ, ψ⟩ = Σ_{τ∈X(k)} ⟨φ_τ, ψ_τ⟩
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex, let $-1\le k<l\le n$, and let $\phi,\psi$ be $l$-cochains. For $\tau\in X(k)$, let $\phi_\tau,\psi_\tau$ be their localizations to the link $X_\tau$, which are $(l-k-1)$-cochains of $X_\tau$, with the inner product of $(X_\tau,m_\tau)$. Then
--   $$\binom{l+1}{k+1}\langle\phi,\psi\rangle=\sum_{\tau\in X(k)}\langle\phi_\tau,\psi_\tau\rangle .$$
--
--   This is the first of Garland's localization identities: global inner products are averages of local ones.
--
--   **Formalization Note.** With $c=k+1$ (the number of vertices of $\tau$), the hypotheses are $c\le l\le n$. The link cochains live on faces of $X_\tau$ with $l+1-c$ vertices; the natural-number subtraction is exact since $c\le l$.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 10, Proposition 4.1 (1) (proof in Appendix A, pp. 28–29)

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting

namespace HighOrderWalks.TwoSided

/-- Proposition 4.1 (1), p. 10: for `-1 ≤ k < l ≤ n` (`c = k + 1 ≤ l`) and `l`-cochains
`φ, ψ`, `binom(l+1, k+1) ⟨φ, ψ⟩ = Σ_{τ ∈ X(k)} ⟨φ_τ, ψ_τ⟩`, the right-hand inner products being
those of the links `X_τ` on `(l - k - 1)`-cochains (faces with `l + 1 - c` vertices). -/
theorem proposition_4_1_1 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (c l : ℕ) (hcl : c ≤ l) (hl : l ≤ n) (φ ψ : Finset V → ℝ) :
    (Nat.choose (l + 1) c : ℝ) * HighOrderWalks.OneSided.ip X m (l + 1) φ ψ =
      ∑ τ ∈ HighOrderWalks.OneSided.cells X c, HighOrderWalks.OneSided.ip (HighOrderWalks.OneSided.link X τ) (HighOrderWalks.OneSided.linkWeight m τ) (l + 1 - c) (HighOrderWalks.OneSided.loc φ τ) (HighOrderWalks.OneSided.loc ψ τ) := by sorry

end HighOrderWalks.TwoSided
