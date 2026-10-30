-- Prove2me | Theorems.Thm_KellyKolmogorov_potential_path_independent
-- name    : KellyKolmogorov.potential_path_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:43:13.122002+00:00
-- url     : https://prove2.me/theorems/519b6fff-808a-4815-88fa-378ee8a12ff6
-- title:
--   Proof of Theorem 1.7 — the potential does not depend on the path
-- statement:
--   Let $\mathcal S$ be a set and $w(j,k)\ge0$ nonnegative weights satisfying Kolmogorov's cycle condition. Let $l$ and $l'$ be two finite sequences of states leading from $j$ to $j_0$ whose forward products $w(j,a_1)w(a_1,a_2)\cdots w(a_m,j_0)$ are positive. Then
--   $$
--   \frac{\text{product of } w \text{ along } l \text{ reversed}}{\text{product of } w \text{ along } l}=\frac{\text{product of } w \text{ along } l' \text{ reversed}}{\text{product of } w \text{ along } l'} .
--   $$
--
--   Hence the potential $\pi(j)=B\,p(j_0,j_1)\cdots p(j_n,j)/\bigl(p(j,j_n)\cdots p(j_1,j_0)\bigr)$ of the proof of Kolmogorov's criterion is well defined.
--
--   Differences from the source:
--   - generalization: path independence of π(j) stated for the transition probabilities p of a Markov chain (proof of Theorem 1.7) → stated for arbitrary nonnegative weights w : 𝒮 → 𝒮 → ℝ≥0; reason: the step uses only the algebra of the products; it specializes to w = p verbatim and to w = q, the 'direct analogue' for a Markov process used by Theorem 1.8 (p. 23)
--   - encoding: a sequence of states j, jn, …, j1, j0 leading from j to j0 and the products p(j, jn)⋯p(j1, j0), p(j0, j1)⋯p(jn, j) → a list l with IsPathFromTo l j j₀, fwdProd w l and revProd w l; reason: lists of states with first and last element fixed; same instances
--   - encoding: π(j) = B · (reverse product)/(forward product) with B > 0 does not depend on the sequence → the ratio revProd w l / fwdProd w l (in ℝ≥0) does not depend on l; reason: the positive constant B cancels; the denominators are positive
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), proof of Theorem 1.7, p. 22 (PDF p. 25)

import Mathlib
import Definitions.Def_KellyKolmogorov_KolmogorovCycle
import Definitions.Def_KellyKolmogorov_fwdProd
import Definitions.Def_KellyKolmogorov_revProd
import Definitions.Def_KellyKolmogorov_IsPathFromTo

open scoped NNReal

namespace KellyKolmogorov

/-- **The potential does not depend on the path.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), proof of Theorem 1.7, p. 22: with
`π(j) = B p(j₀, j₁)p(j₁, j₂) ⋯ p(jₙ, j) / (p(j, jₙ)p(jₙ, jₙ₋₁) ⋯ p(j₁, j₀))`, "Observe that
`π(j)` does not depend upon the particular sequence of states chosen to lead from `j` to `j₀`".

For nonnegative weights `w` satisfying Kolmogorov's cycle condition, and two sequences of states
`l`, `l'` from `j` to `j₀` with positive forward products, the ratio of the backward product to
the forward product is the same for `l` and `l'`. -/
theorem potential_path_independent {𝒮 : Type*} (w : 𝒮 → 𝒮 → ℝ≥0) (hw : KolmogorovCycle w)
    (l l' : List 𝒮) (j j₀ : 𝒮) (hl : IsPathFromTo l j j₀) (hl' : IsPathFromTo l' j j₀)
    (hpos : 0 < fwdProd w l) (hpos' : 0 < fwdProd w l') :
    revProd w l / fwdProd w l = revProd w l' / fwdProd w l' := by sorry

end KellyKolmogorov
