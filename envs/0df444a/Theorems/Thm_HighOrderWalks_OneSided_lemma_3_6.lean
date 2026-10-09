-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_lemma_3_6
-- name    : HighOrderWalks.OneSided.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:02.586461+00:00
-- url     : https://prove2.me/theorems/523fd3aa-ee93-443d-97d4-e9c0c8d0055d
-- title:
--   Lemma 3.6, p. 8 — d*ψ(τ) = Σ_{σ⊃τ} (m(σ)/m(τ)) ψ(σ) is the adjoint of the signless differential
-- statement:
--   Let $X$ be a finite simplicial complex with a weight function $m$, and let $-1\le k\le n-1$. For a $(k+1)$-cochain $\psi$ define
--   $$d^*\psi(\tau)=\sum_{\sigma\in X(k+1),\ \tau\subset\sigma}\frac{m(\sigma)}{m(\tau)}\,\psi(\sigma),\qquad \tau\in X(k).$$
--   Then $d^*$ is the adjoint of the signless differential $d_k$: for every $k$-cochain $\phi$ and every $(k+1)$-cochain $\psi$,
--   $$\langle d_k\phi,\psi\rangle=\langle\phi,d^*\psi\rangle .$$
--
--   This identifies the abstractly defined adjoint $(d_k)^*$ of Definition 3.4 with an explicit averaging formula, which every later computation uses.
--
--   **Formalization Note.** The complex is not assumed pure (the standing hypothesis `IsPureComplex` is dropped, which makes the statement stronger); only the positivity and balance of $m$ (`IsWeight`) are assumed. $c=k+1$ is the number of vertices of a $k$-face, and $c\le n$ is $k\le n-1$.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 8, Lemma 3.6

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Lemma 3.6, p. 8: for `-1 ≤ k ≤ n - 1` (`c = k + 1 ≤ n`), the operator `d*` given by
`d*ψ(τ) = Σ_{σ ∈ X(k+1), τ ⊂ σ} (m(σ)/m(τ)) ψ(σ)` is the adjoint of the signless differential:
`⟨dφ, ψ⟩ = ⟨φ, d*ψ⟩`. -/
theorem lemma_3_6 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m) (c : ℕ) (hc : c ≤ n)
    (φ ψ : Finset V → ℝ) :
    ip X m (c + 1) (dS X φ) ψ = ip X m c φ (dStar X m ψ) := by sorry

end HighOrderWalks.OneSided
