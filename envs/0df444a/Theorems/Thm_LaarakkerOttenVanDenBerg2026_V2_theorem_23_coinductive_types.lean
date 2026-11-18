-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_V2_theorem_23_coinductive_types
-- name    : LaarakkerOttenVanDenBerg2026.V2.theorem_23_coinductive_types
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-17T07:43:49.198693+00:00
-- url     : https://prove2.me/theorems/0f9af43d-988d-42a8-914b-d1627a83d205
-- title:
--   Theorem 23 and preceding lemmas: Canonical coinductive encodings
-- statement:
--   The dual sized infrastructure uses the prescribed bounded-universal modality, its underlying morphism laws, and the recursively constructed internally terminal sized coalgebra. Constant size-indexing and universal quantification lift full coalgebra morphisms with their prescribed underlying actions. For every wild functor weakly commuting with the universal quantifier, the specified coalgebra on $\nu F := \forall i.\,(\nu^\Box F)(i)$ is internally terminal and its structure map is an internal half-adjoint equivalence. All small polynomial signatures supply the required functor and weak-commutation witnesses, including infinitely branching signatures. The lifting laws concern underlying arrows and do not impose unspecified higher coherence on square witnesses.
-- source:
--   Laarakker, Otten and van den Berg, Constructing (Co)inductive Types via Large Sizes, arXiv:2602.18921v2, Section 3 and Appendix B: Proposition 5, Lemmas 19–20, Proposition 22, Theorem 23, polynomial corollary, https://arxiv.org/abs/2602.18921v2

import Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingRevision2

namespace LaarakkerOttenVanDenBerg2026.V2

universe u v w t
open Theory

theorem theorem_23_coinductive_types {C : CwF.{u,v,w,t}} (T : ParametricTheory C) :
    T.toCoreTheory.CoinductiveInfrastructure ∧
    (∀ (Γ : C.Ctx) (D : WildEndofunctor T.univ T.functions T.identities Γ)
      (h : T.toCoreTheory.WeaklyCommutesAll D),
      T.toCoreTheory.CoinductiveEncoding D h) ∧
    T.toCoreTheory.PolynomialCoinductiveEncodings := by
  sorry

end LaarakkerOttenVanDenBerg2026.V2
