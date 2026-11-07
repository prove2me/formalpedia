-- Prove2me | Theorems.Thm_FourColorLinear_greedy_survivors
-- name    : FourColorLinear.greedy_survivors
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:58.699197+00:00
-- url     : https://prove2.me/theorems/79dbbe02-f541-4527-b008-b6a5d5210da7
-- title:
--   Greedy swap decisions keep at least $q/(3\cdot 2^{R})$ rings (Proof of Lemma 4, (1))
-- statement:
--   Let each of $q$ rings have a preferred pairing among three and, for that pairing, preferred swaps on at most $R$ chains. Let $a$ be a most preferred pairing, and let $\Phi(\mathrm{Dec},\mathrm{val})=\sum_{R_i\text{ live}}2^{-u_i}$ be the potential (1). Then
--
--   1. for any undecided chain $x$, one of the two decisions on $x$ does not decrease $\Phi$;
--   2. $\Phi$ is always an integer multiple of $1/2^R$;
--   3. processing chains in any order, with every decision non-decreasing, ends with at least as many live rings as the original expectation $\Phi(\emptyset)=\sum_{R_i\text{ live}}2^{-|\tau_i|}$, hence at least $q/(3\cdot 2^R)$ live rings, whose decided chains agree with their wishes.
--
--   This is the counting at the heart of Lemma 4 and Lemma 11, with no graph in it: $R=18$ gives the fraction $p=1/(3\cdot 2^{18})$.
--
--   Differences from the source:
--   - generalization: |R_i| ≤ 18 and Kempe chains of a graph → any bound R, and abstract chains intersecting rings; reason: the argument only counts; the printed case is R = 18
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), Proof of Lemma 4, (1), pp.7–8; §3, p.19

import Mathlib
import Definitions.Def_FourColorLinear_greedyPotential

namespace FourColorLinear

/-- The greedy derandomization of arXiv:2610.39753 (held version, sha256 4dce39c5…), Proof of Lemma 4, pp.7–8, with p.19: "We now go through
each Kempe chain using the selected color pairs and decide whether to swap the colors. … Thus,
conditioned on decisions made, the expected number of survivors is Σ_{Ri is still live} 2^{−ui}, where
ui is the number of undecided chains intersecting Ri. (1) We can now pick any undecided Kempe chain X.
We know that one of the two choices — swap or no-swap — will not decrease the conditional expectation
… we conclude that the final set of live rings is at least as big as the original expectation." With
p.19: "we note that the expectancy is always an integer multiple of 1/2^18".

**Formalization Note** The combinatorial content, with no graph: each ring wishes one of 3 pairings
and, for the chains `χ a` of a pairing `a`, swaps on at most `R` chains. `a` is a commonest wish. For
every processing order and every non-decreasing sequence of choices, the final number of live rings
is at least the original expectation `greedyPotential alive₀ (τ a) (σ a) ∅ val`, hence at least
`|ι|/(3·2^R)`. `R = 18` is the printed bound. -/
theorem greedy_survivors {ι : Type} [Fintype ι] [DecidableEq ι] {χ : Fin 3 → Type}
    [∀ a, DecidableEq (χ a)] (R : ℕ) (pw : ι → Fin 3)
    (τ : ∀ a, ι → Finset (χ a)) (σ : ∀ a, ι → χ a → Bool) (hτ : ∀ a i, (τ a i).card ≤ R)
    (a : Fin 3)
    (ha : ∀ b, (Finset.univ.filter fun i => pw i = b).card ≤
      (Finset.univ.filter fun i => pw i = a).card) :
    let alive₀ : Finset ι := Finset.univ.filter fun i => pw i = a
    (∀ (Dec : Finset (χ a)) (val : χ a → Bool) (x : χ a), x ∉ Dec →
      ∃ b, greedyPotential alive₀ (τ a) (σ a) Dec val ≤
        greedyPotential alive₀ (τ a) (σ a) (insert x Dec) (Function.update val x b)) ∧
    (∀ (Dec : Finset (χ a)) (val : χ a → Bool),
      ∃ m : ℕ, greedyPotential alive₀ (τ a) (σ a) Dec val = m / 2 ^ R) ∧
    ∀ (ord : List (χ a)) (val : χ a → Bool), ord.Nodup →
      (∀ k < ord.length,
        greedyPotential alive₀ (τ a) (σ a) (ord.take k).toFinset val ≤
          greedyPotential alive₀ (τ a) (σ a) (ord.take (k + 1)).toFinset val) →
      greedyPotential alive₀ (τ a) (σ a) ∅ val ≤
        ((liveRings alive₀ (τ a) (σ a) ord.toFinset val).card : ℚ) ∧
      Fintype.card ι ≤
        3 * 2 ^ R * (liveRings alive₀ (τ a) (σ a) ord.toFinset val).card ∧
      (∀ i ∈ liveRings alive₀ (τ a) (σ a) ord.toFinset val, τ a i ⊆ ord.toFinset →
        ∀ x ∈ τ a i, val x = σ a i x) := by sorry

end FourColorLinear
