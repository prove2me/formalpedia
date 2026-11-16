-- Prove2me | Theorems.Thm_GreedyColoringLCA969_LowerBound_Supplement_lemma_4_7
-- name    : GreedyColoringLCA969.LowerBound.Supplement.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:34:07.746913+00:00
-- url     : https://prove2.me/theorems/8f74b45f-1e76-42b3-8165-763375acc4ca
-- title:
--   Lemma 4.7 — Local configurations remain valid after adjoining any multiset of spawned labels; both assertions, for arbitrary L.
-- statement:
--   Let $L$ be any label set, $P$ a labeling problem on all finite simple graphs, $F:\operatorname{Mult}(L)\to L$ an extension rule, and $C$ a radius-one local verifier for $P$. Assume every label of $L$ is produced by $F$ on some graph in some vertex ordering. Then both statements hold:
--
--   1. For every finite multiset $S$, $(F(S),S)\in C$.
--   2. For all finite multisets $S,T$, if $F(S)\rightsquigarrow\alpha$ for every $\alpha$ occurring in $T$, then
--
--   $$ (F(S),S\uplus T)\in C.$$
--
--   The two assertions describe exactly the local views that remain acceptable as spawned labels are added. No finiteness hypothesis on $L$ is imposed.
--
--   Differences from the source:
--   - encoding: all finite graphs and arbitrary orderings, with multiset union → graphs on Fin n, permutations of Fin n, and Multiset addition; reason: every finite labeled graph and ordering is represented; addition preserves multiplicities
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), p. 17 (PDF 18), Lemma 4.7

import Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_Labeling

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

theorem lemma_4_7 {L : Type} (P : LabelProblem L) (F : Multiset L → L)
    (C : Set (L × Multiset L)) (hext : IsExtensionRule P F)
    (hloc : IsLocalVerifier P C) (hreal : AllLabelsRealizable F) :
    (∀ S : Multiset L, (F S, S) ∈ C) ∧
    (∀ S T : Multiset L, (∀ α ∈ T, Spawns F (F S) α) → (F S, S + T) ∈ C) := by sorry

end GreedyColoringLCA969.LowerBound.Supplement
