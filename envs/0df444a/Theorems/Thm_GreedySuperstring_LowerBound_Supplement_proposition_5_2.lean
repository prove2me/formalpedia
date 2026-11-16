-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_proposition_5_2
-- name    : GreedySuperstring.LowerBound.Supplement.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:43:53.562321+00:00
-- url     : https://prove2.me/theorems/3cc4a27b-198c-4dc9-accc-e24200ceeded
-- title:
--   Proposition 5.2 — the bound $9/5$ is tight on strings of length three
-- statement:
--   1. For every integer $\ell\ge1$ there is a set $S$ of exactly $5\ell$ words of length three that has a common superstring $H$ with $|H|=5\ell+2$, whereas the greedy algorithm, for some way of breaking ties, outputs a common superstring $g$ of $S$ with $|g|=9\ell$.
--   2. Consequently $\rho_3\ge9/5$: for every real $c<9/5$ there are a nonempty set $S$ of words of length three and an output $g$ of the greedy algorithm on $S$ with
--
--   $$c\cdot\mathrm{OPT}(S)<|g|.$$
--
--   With Theorem 5.1 this gives $\rho_3=9/5$.
--
--   Differences from the source:
--   - encoding: strings over a finite alphabet with ℓ + 2 symbols → words over the published Symbol carrier; reason: each instance uses finitely many symbols; renaming them to a finite alphabet changes no length or overlap, and OPT is unchanged since a shortest superstring can be taken over the occurring symbols
--   - encoding: the greedy algorithm may output g → IsGreedyOutput S g, existence of a complete greedy run ending at g; reason: the paper defines 'may' as some way of breaking ties (p.23)
--   - encoding: ρ₃ ≥ 9/5 for the supremum ρ₃ of |g|/OPT → for every real c < 9/5, an instance and a greedy output with c·OPT < |g|; reason: for positive OPT this is exactly the supremum bound, without defining the supremum
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Proposition 5.2, printed p.23 = PDF p.23; proof pp.24–25; ρ_k defined p.23

import Mathlib
import Definitions.Def_Superstring
import Definitions.Def_GreedySuperstring_LowerBound_GreedyModel

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

/-- Proposition 5.2, printed/PDF p.23. (a) For every `ℓ ≥ 1` there is a set of exactly `5ℓ`
words of length three with a common superstring of length `5ℓ + 2`, on which some greedy run
outputs a common superstring of length `9ℓ`. (b) `ρ₃ ≥ 9/5`, in supremum-free form: for every
real `c < 9/5` some nonempty set of length-three words has a greedy output `g` with
`c · OPT < |g|`. Words are over the published `Symbol` alphabet. -/
theorem proposition_5_2 :
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      ∃ (S : Finset OAI.Superstring.Word) (H g : OAI.Superstring.Word),
        S.card = 5 * ℓ ∧ (∀ s ∈ S, s.length = 3) ∧
        OAI.Superstring.IsCommonSuperstring S.toList H ∧ H.length = 5 * ℓ + 2 ∧
        OAI.Superstring.IsCommonSuperstring S.toList g ∧ IsGreedyOutput S g ∧
        g.length = 9 * ℓ) ∧
    (∀ c : ℝ, c < 9 / 5 →
      ∃ (S : Finset OAI.Superstring.Word) (g : OAI.Superstring.Word),
        S.Nonempty ∧ (∀ s ∈ S, s.length = 3) ∧ IsGreedyOutput S g ∧
        c * ((OAI.Superstring.opt S.toList : ℕ) : ℝ) < ((g.length : ℕ) : ℝ)) := by sorry

end GreedySuperstring.LowerBound.Supplement
