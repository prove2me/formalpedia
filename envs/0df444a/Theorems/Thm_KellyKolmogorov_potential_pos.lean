-- Prove2me | Theorems.Thm_KellyKolmogorov_potential_pos
-- name    : KellyKolmogorov.potential_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:43:41.236558+00:00
-- url     : https://prove2.me/theorems/5620c46f-d2d1-425e-90a6-096f18dafa6e
-- title:
--   Proof of Theorem 1.7 — the potential is positive
-- statement:
--   Let $\mathcal S$ be a set and $w(j,k)\ge0$ nonnegative weights that satisfy Kolmogorov's cycle condition and are irreducible: between any two states there is a finite sequence of states with positive product of weights along it. If a sequence $l$ leads from $j$ to $j_0$ and the product of $w$ along $l$ is positive, then the product of $w$ along $l$ traversed backwards is also positive.
--
--   Consequently the potential $\pi(j)=B\cdot(\text{backward product})/(\text{forward product})$, $B>0$, is positive.
--
--   Differences from the source:
--   - generalization: positivity of π(j) stated for the transition probabilities p of a Markov chain (proof of Theorem 1.7) → stated for arbitrary nonnegative weights w : 𝒮 → 𝒮 → ℝ≥0; reason: the step uses only the algebra of the products; it specializes to w = p verbatim and to w = q, the 'direct analogue' for a Markov process used by Theorem 1.8 (p. 23)
--   - encoding: a sequence of states j, jn, …, j1, j0 leading from j to j0 and the products p(j, jn)⋯p(j1, j0), p(j0, j1)⋯p(jn, j) → a list l with IsPathFromTo l j j₀, fwdProd w l and revProd w l; reason: lists of states with first and last element fixed; same instances
--   - reading: irreducibility (of the chain) → for all a, b there is a sequence from a to b with positive forward product of w; reason: the positive-weight form of irreducibility that the step uses; for the rates of an irreducible process it is supplied by exists_positive_rate_path
--   - encoding: π(j) = B · (reverse product)/(forward product) is positive → revProd w l > 0; reason: B > 0 and the forward product is positive, so the two are equivalent
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), proof of Theorem 1.7, p. 22 (PDF p. 25)

import Mathlib
import Definitions.Def_KellyKolmogorov_KolmogorovCycle
import Definitions.Def_KellyKolmogorov_fwdProd
import Definitions.Def_KellyKolmogorov_revProd
import Definitions.Def_KellyKolmogorov_IsPathFromTo

open scoped NNReal

namespace KellyKolmogorov

/-- **The potential is positive.**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), proof of Theorem 1.7, p. 22: "Note
that irreducibility and relation (1.21) imply that `π(j)` is positive."

Let `w` be nonnegative weights satisfying Kolmogorov's cycle condition and irreducible in the
sense that between any two states there is a sequence of states with positive forward product.
Then every sequence `l` from `j` to `j₀` with positive forward product also has positive
backward product, so `π(j) = B · revProd / fwdProd > 0`. -/
theorem potential_pos {𝒮 : Type*} (w : 𝒮 → 𝒮 → ℝ≥0) (hw : KolmogorovCycle w)
    (hirr : ∀ a b : 𝒮, ∃ l : List 𝒮, IsPathFromTo l a b ∧ 0 < fwdProd w l)
    (l : List 𝒮) (j j₀ : 𝒮) (hl : IsPathFromTo l j j₀) (hpos : 0 < fwdProd w l) :
    0 < revProd w l := by sorry

end KellyKolmogorov
