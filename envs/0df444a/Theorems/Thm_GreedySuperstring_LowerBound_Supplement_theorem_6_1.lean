-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_theorem_6_1
-- name    : GreedySuperstring.LowerBound.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:44:18.613569+00:00
-- url     : https://prove2.me/theorems/16fa6d5d-26c0-43ea-8aa6-d30676487db1
-- title:
--   Theorem 6.1 — $\rho_k\ge2$ for strings of every length $k\ge6$
-- statement:
--   1. For all integers $k\ge6$ and $\ell\ge1$ there is a set $S$ of exactly $(2k-3)\ell$ words of length $k$ that has a common superstring $H$ with $|H|=(2k-3)\ell+k-1$, whereas the greedy algorithm, for some way of breaking ties, outputs a common superstring $g$ of $S$ with $|g|=(4k-6)\ell$.
--   2. Consequently $\rho_k\ge2$ for every $k\ge6$: for every $k\ge6$ and every real $c<2$ there are a nonempty set $S$ of words of length $k$ and an output $g$ of the greedy algorithm on $S$ with
--
--   $$c\cdot\mathrm{OPT}(S)<|g|.$$
--
--   Thus, whereas greedy is a $9/5$-approximation on strings of length three (Theorem 5.1), its approximation ratio on strings of any fixed length $k\ge6$ is at least $2$.
--
--   Differences from the source:
--   - encoding: strings over a finite alphabet with ℓ + 3 symbols → words over the published Symbol carrier; reason: each instance uses finitely many symbols; renaming them to a finite alphabet changes no length or overlap, and OPT is unchanged since a shortest superstring can be taken over the occurring symbols
--   - encoding: the greedy algorithm may output g → IsGreedyOutput S g, existence of a complete greedy run ending at g; reason: the paper defines 'may' as some way of breaking ties (p.33)
--   - encoding: ρ_k ≥ 2 for the supremum ρ_k of |g|/OPT → for every k ≥ 6 and real c < 2, an instance and a greedy output with c·OPT < |g|; reason: for positive OPT this is exactly the supremum bound, without defining the supremum
--   - encoding: (2k − 3)ℓ, (2k − 3)ℓ + k − 1 and (4k − 6)ℓ over the integers → the same expressions in ℕ; reason: k ≥ 6 makes every subtraction exact
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Theorem 6.1, printed p.33 = PDF p.33; proof p.34; ρ_k defined p.23

import Mathlib
import Definitions.Def_Superstring
import Definitions.Def_GreedySuperstring_LowerBound_GreedyModel

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Theorem 6.1, printed/PDF p.33. (a) For all `k ≥ 6` and `ℓ ≥ 1` there is a set of exactly
`(2k − 3)ℓ` words of length `k` with a common superstring of length `(2k − 3)ℓ + k − 1`, on
which some greedy run outputs a common superstring of length `(4k − 6)ℓ`. (b) `ρ_k ≥ 2` for
every `k ≥ 6`, in supremum-free form. All subtractions are of a smaller from a larger number
since `k ≥ 6`. Words are over the published `Symbol` alphabet. -/
theorem theorem_6_1 :
    (∀ k ℓ : ℕ, 6 ≤ k → 1 ≤ ℓ →
      ∃ (S : Finset OAI.Superstring.Word) (H g : OAI.Superstring.Word),
        S.card = (2 * k - 3) * ℓ ∧ (∀ s ∈ S, s.length = k) ∧
        OAI.Superstring.IsCommonSuperstring S.toList H ∧
        H.length = (2 * k - 3) * ℓ + k - 1 ∧
        OAI.Superstring.IsCommonSuperstring S.toList g ∧ IsGreedyOutput S g ∧
        g.length = (4 * k - 6) * ℓ) ∧
    (∀ k : ℕ, 6 ≤ k → ∀ c : ℝ, c < 2 →
      ∃ (S : Finset OAI.Superstring.Word) (g : OAI.Superstring.Word),
        S.Nonempty ∧ (∀ s ∈ S, s.length = k) ∧ IsGreedyOutput S g ∧
        c * ((OAI.Superstring.opt S.toList : ℕ) : ℝ) < ((g.length : ℕ) : ℝ)) := by sorry

end GreedySuperstring.LowerBound.Supplement
