-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_V2_theorem_11_inductive_types
-- name    : LaarakkerOttenVanDenBerg2026.V2.theorem_11_inductive_types
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-17T07:43:41.013435+00:00
-- url     : https://prove2.me/theorems/11e739f8-4651-4c8a-975e-c38f104fe8ea
-- title:
--   Theorem 11: Canonical inductive encodings and polynomial W-types
-- statement:
--   For every contextual wild functor with the internally quantified existential weak-commutation witness, the prescribed algebra on $\mu F := \exists i.\,(\mu^\Diamond F)(i)$ is internally initial and its prescribed structure map is an internal half-adjoint equivalence. Every small polynomial signature supplies functor-law witnesses for the literal polynomial object and morphism data, the required weak-commutation witness, and this canonical initial algebra. No finiteness or inhabitedness restriction is imposed on the branching types.
-- source:
--   Laarakker, Otten and van den Berg, Constructing (Co)inductive Types via Large Sizes, arXiv:2602.18921v2, Section 3, Theorem 11 and polynomial corollary, https://arxiv.org/abs/2602.18921v2

import Definitions.Def_LaarakkerOttenVanDenBerg2026_EncodingRevision2

namespace LaarakkerOttenVanDenBerg2026.V2

universe u v w t
open Theory

/-- The prescribed existential encoding is an initial algebra for every
weakly commuting wild functor, and every polynomial signature supplies the
needed functor and weak-commutation witnesses. -/
theorem theorem_11_inductive_types {C : CwF.{u,v,w,t}} (T : ParametricTheory C) :
    (∀ (Γ : C.Ctx) (D : WildEndofunctor T.univ T.functions T.identities Γ)
      (h : T.toCoreTheory.WeaklyCommutesExists D),
      T.toCoreTheory.InductiveEncoding D h) ∧
    T.toCoreTheory.PolynomialInductiveEncodings := by
  sorry

end LaarakkerOttenVanDenBerg2026.V2
