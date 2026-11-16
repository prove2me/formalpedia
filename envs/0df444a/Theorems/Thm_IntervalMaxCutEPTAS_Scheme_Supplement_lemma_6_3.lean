-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_Supplement_lemma_6_3
-- name    : IntervalMaxCutEPTAS.Scheme.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:47.55806+00:00
-- url     : https://prove2.me/theorems/c8519b3c-f2d9-4587-ad53-3eefd05d2339
-- title:
--   Lemma 6.3 (used in the proof of Theorem 1.2) — polynomial expression construction
-- statement:
--   There is one deterministic program, with absolute polynomial constants fixed before all instances, that takes a supplied structure of Proposition 4.10 and nonnegative integers $K,J$ bounding every valid cell by $K(C)\le K$ and $|A(C)|\le J$. The graph $H$ has an expression using exactly the available label palette
--
--   $$w=3K+J+1.$$
--
--   The program outputs an adjacency bitmap and a valid expression for this same $H$, with an explicit leaf bijection, in time and space at most $C(n+K+J+1)^d$ for absolute constants. The input is $n,b,K,J$ followed by the published structure serialization. The word capacity may depend on $b$, while the time polynomial does not. This is the constructive palette lemma for Theorem 1.2.
--
--   Differences from the source:
--   - encoding: the structure fixed in Proposition 4.10 with b ≥ 4 and its good shift → the published Setup, valid heap cell indices, group representative ids and GoodShift; reason: these are the same constructed objects and standing assumptions; no geometric or density condition is added
--   - encoding: a clique-width expression, without excluding the empty graph → the published positive expressions plus an empty expression evaluated only on Empty; reason: this covers n = 0; identity relabeling allowed by the published language changes no graph or width
--   - reading: word-RAM operations on words of Θ(log n) bits, including accuracy and output addresses → charged Light operations with polynomial word capacity in the numeric input parameters and addresses; reason: the construction manipulates the accuracy and its polynomial-size output; this is the same transdichotomous word convention as the immutable base mission
--   - encoding: compute the graph and a width expression → the fixed prefix packet of width, adjacency matrix, expression and explicit leaf names; reason: the executable parser and published expression evaluation fix the meaning of every output word independently of the theorem
--   - encoding: polynomial time in n,K,J → uniform Light execution bounded by C(n+K+J+1)^d, with space bounded by the same polynomial; reason: all operations are charged and a polynomial-time execution touches at most polynomially many cells
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 6.3, PDF p. 24 (printed p. 23)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_WidthMachine

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

/-- Lemma 6.3, PDF 24 (printed 23). The supplied structure is input, the program is uniform,
and b affects word capacity but not the polynomial time bound in n,K,J. -/
theorem lemma_6_3 :
    ∃ (Prog : Light.Program) (C d c : ℕ), 0 < C ∧ 1 ≤ d ∧ 1 ≤ c ∧
      ∀ (n K J : ℕ) (P : Setup n), 4 ≤ P.b → P.θ < 2 * bigM n → GoodShift P →
        (∀ a, IsCell n a → neighborhoodCount P a ≤ K ∧ (own P a).card ≤ J) →
        HasExpression (H P) (3 * K + J + 1) ∧
        ∃ T S : ℕ, T ≤ C * (n + K + J + 1) ^ d ∧ S ≤ C * (n + K + J + 1) ^ d ∧
          Light.Ends ⟨((n + P.b + K + J + 2) ^ c : ℕ), S, T⟩ Prog 0 entry
            (start (encodeExpression P K J)) T
            (ReportsExpression (H P) (3 * K + J + 1) S) := by sorry

end IntervalMaxCutEPTAS.Scheme.Supplement
