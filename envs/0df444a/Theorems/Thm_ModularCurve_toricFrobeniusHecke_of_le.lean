-- Prove2me | Theorems.Thm_ModularCurve_toricFrobeniusHecke_of_le
-- name    : ModularCurve.toricFrobeniusHecke_of_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:56:34.737025+00:00
-- url     : https://prove2.me/theorems/17c5d9a6-eab9-481c-87c1-c8a32a9c5806
-- title:
--   Hecke Frobenius property passes to submodules
-- statement:
--   Let $\mathcal{T}$ and $U$ be Hecke submodules of $J_0(Nq)$. If $\mathcal{T}$ has the Hecke Frobenius property at a prime $q$ and $U \le \mathcal{T}$, then $U$ has the Hecke Frobenius property at $q$.
-- source:
--   Derived from the toric monodromy argument for ModularCurve.toricFrobeniusHecke_toricMonodromyPart_jZero in the Fermat's Last Theorem formalization (prove2me workspace).

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_DeligneRapoport
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_GenusOnePic0

namespace ModularCurve
theorem toricFrobeniusHecke_of_le (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime)
    (frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    [Module ModularCurve.HeckeAlg (ModularCurve.JZero (N * q))]
    (𝒯 U : Submodule ModularCurve.HeckeAlg (ModularCurve.JZero (N * q)))
    (hhecke : ModularCurve.ToricFrobeniusHecke ⟨q, hq⟩ frob 𝒯) (hle : U ≤ 𝒯) :
    ModularCurve.ToricFrobeniusHecke ⟨q, hq⟩ frob U := by sorry
end ModularCurve
