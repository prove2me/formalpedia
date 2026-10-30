-- Prove2me | Theorems.Thm_KellyKolmogorov_detailedBalance_kolmogorovCycle
-- name    : KellyKolmogorov.detailedBalance_kolmogorovCycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:41:56.613498+00:00
-- url     : https://prove2.me/theorems/9e651987-4401-4502-b1c8-6432c5ff25d3
-- title:
--   Proof of Theorem 1.7 — detailed balance implies Kolmogorov's cycle condition
-- statement:
--   Let $\mathcal S$ be a set and $w(j,k)\ge0$, $j,k\in\mathcal S$, nonnegative weights (for instance transition probabilities $p$ of a Markov chain or transition rates $q$ of a Markov process). If a collection of positive numbers $\pi(j)$, $j\in\mathcal S$, satisfies the detailed balance conditions $\pi(j)w(j,k)=\pi(k)w(k,j)$ for all $j,k$, then for every finite sequence of states $j_1,\dots,j_n$
--   $$
--   w(j_1,j_2)\,w(j_2,j_3)\cdots w(j_n,j_1)=w(j_1,j_n)\,w(j_n,j_{n-1})\cdots w(j_2,j_1).
--   $$
--
--   This is the first half of the proof of Kolmogorov's criterion: multiplying the detailed balance conditions around a cycle and cancelling the positive numbers $\pi(j)$.
--
--   Differences from the source:
--   - generalization: the multiplication step stated for the transition probabilities p of a Markov chain (proof of Theorem 1.7) → stated for arbitrary nonnegative weights w : 𝒮 → 𝒮 → ℝ≥0; reason: the step uses only the algebra of the products; it specializes to w = p verbatim and to w = q, the 'direct analogue' for a Markov process used by Theorem 1.8 (p. 23)
--   - generalization: π the (positive) equilibrium probabilities of a reversible chain → any family of positive reals π satisfying detailed balance for w; reason: the step uses only positivity of π and detailed balance; the equilibrium probabilities are such a family
--   - encoding: any finite sequence of states j1, …, jn ∈ 𝒮 and the closed product q(j1, j2)⋯q(jn, j1) → every j : Fin (n+1) → 𝒮, with finRotate (n+1) as the cyclic successor; reason: Fin (n+1) covers every length n+1 ≥ 1; same instances
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), proof of Theorem 1.7, p. 22 (PDF p. 25), first paragraph; carried over to rates on p. 23

import Mathlib
import Definitions.Def_KellyKolmogorov_DetailedBalance
import Definitions.Def_KellyKolmogorov_KolmogorovCycle

open scoped NNReal

namespace KellyKolmogorov

/-- **Detailed balance implies Kolmogorov's cycle condition.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), proof of Theorem 1.7, p. 22: "If the
process is reversible then the detailed balance conditions hold; hence
`π(j₁)p(j₁, j₂) = π(j₂)p(j₂, j₁)`, …, `π(jₙ)p(jₙ, j₁) = π(j₁)p(j₁, jₙ)`. Multiplying these
conditions together and cancelling the positive equilibrium probabilities gives equation (1.21)."

For any nonnegative weights `w` (transition probabilities `p` or transition rates `q`): if a family
of positive numbers `π` satisfies the detailed balance conditions for `w`, then `w` satisfies
Kolmogorov's cycle condition. -/
theorem detailedBalance_kolmogorovCycle {𝒮 : Type*} (w : 𝒮 → 𝒮 → ℝ≥0) (π : 𝒮 → ℝ)
    (hπ : ∀ j, 0 < π j) (h : DetailedBalance π w) : KolmogorovCycle w := by sorry

end KellyKolmogorov
