-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_4_4
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:17.958413+00:00
-- url     : https://prove2.me/theorems/4c6a52a1-4b0b-424e-a48e-a29d9b741191
-- title:
--   Lemma 4.4 — at most 28σm edges are deleted
-- statement:
--   Let $b\ge4$, $\sigma=2^{-b}$, and let the shift $\theta$ satisfy the bound of Lemma 4.2. Then the edited graph $H$ is a spanning subgraph of $G$ and
--
--   $$|E(G)\setminus E(H)|\le 28\sigma m.$$
--
--   Differences from the source:
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
--   - encoding: σ = 2^{-b} in inequalities → inequalities multiplied out by powers of two in ℕ/ℤ; reason: exact equivalence: σ is an exact power of two, nothing is rounded
--   - encoding: θ fixed as in Lemma 4.2 → hypothesis GoodShift P (2^b·Σ_{v∈Z} deg v ≤ 4m) and θ < 2M; reason: the same assumption, written out; the source's proof uses exactly this bound
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 4.4, PDF p. 16 (printed p. 15); proof to PDF p. 17

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 4.4: if the shift satisfies the bound of Lemma 4.2, then `H` is a spanning subgraph
of `G` and `|E(G) \ E(H)| ≤ 28σm`. -/
theorem lemma_4_4 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b) (hθ : P.θ < 2 * bigM n)
    (hgood : GoodShift P) :
    H P ≤ P.G ∧
      2 ^ P.b * (P.G.edgeFinset \ (H P).edgeFinset).card ≤ 28 * P.G.edgeFinset.card := by sorry

end IntervalMaxCutEPTAS.Scheme
