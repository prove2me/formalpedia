-- Prove2me | Theorems.Thm_OptimalPAC_SampleComplexity_subsamples_subset
-- name    : OptimalPAC.SampleComplexity.subsamples_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:28:04.565001+00:00
-- url     : https://prove2.me/theorems/c125dfcc-7b3b-4d78-8784-d633e22eb080
-- title:
--   Every subsample of $\mathbb A(S;T)$ lies between $T$ and $S\cup T$; the number of subsamples does not depend on $T$
-- statement:
--   For all finite sequences $S$ and $T$ of points in $\mathcal X\times\mathcal Y$:
--
--   1. every subsample $\hat S$ in the sequence returned by $\mathbb A(S;T)$ satisfies
--   $$T\subseteq\hat S\subseteq S\cup T,$$
--   where $A\subseteq B$ for sequences means that every element of $A$ is an element of $B$;
--   2. the number of subsamples returned by $\mathbb A(S;T)$ is the same for every $T$.
--
--   These are the structural facts used throughout the proof of Theorem 2: containment makes $L$ well defined on every subsample and makes every trained classifier consistent with $T$; equal counts give the three recursive calls equal weight in the majority vote.
-- source:
--   Hanneke, The Optimal Sample Complexity of PAC Learning, arXiv:1507.00473v4, proof of Theorem 2, p. 8 (second paragraph) and p. 10 (each A(S_0;T_j) supplies an equal number of entries)

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model
import Definitions.Def_OptimalPAC_SampleComplexity_Algorithm

namespace OptimalPAC.SampleComplexity

/-- Proof of Theorem 2 (Hanneke 2016, p. 8, and p. 10): for any finite sequences `S`, `T`, every
subsample `Ŝ` returned by `𝔸(S; T)` satisfies `Ŝ ⊆ S ∪ T` and `Ŝ ⊇ T` (as sequences: every
element of one is an element of the other, p. 2); moreover the number of subsamples returned by
`𝔸(S; T)` does not depend on `T`. -/
theorem subsamples_subset {X : Type*} (S T : List (X × Bool)) :
    (∀ Ŝ ∈ subsamples S T, (∀ z ∈ Ŝ, z ∈ S ++ T) ∧ (∀ z ∈ T, z ∈ Ŝ)) ∧
      ∀ T' : List (X × Bool), (subsamples S T).length = (subsamples S T').length := by sorry

end OptimalPAC.SampleComplexity
