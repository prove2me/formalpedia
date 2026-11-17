-- Prove2me | Theorems.Thm_N25_Endgame_FBaseCoeffMap25_frobenius_iterate
-- name    : N25.Endgame.FBaseCoeffMap25_frobenius_iterate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:00.163661+00:00
-- url     : https://prove2.me/theorems/430cdc99-69b8-4422-8e3a-af0b85237b99
-- title:
--   Finite-field Frobenius iteration is the cardinality power map
-- statement:
--   Let $p$ be prime, let $k$ be a finite field of characteristic $p$, let $K$ be a field of characteristic $p$ with a $k$-algebra structure, and suppose $|k|=p^n$. Let $c:F_k→F_K$ be coefficient extension and let $Φ_p$ be $q$-expansion Frobenius on $F_K$. Then for every $x∈F_k$,
--
--   $$Φ_p^n(c(x))=c(x^{|k|}).$$
--
--   This identifies the relevant Frobenius iterate with the intrinsic finite-field cardinality power.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

open N25
open N25.Endgame

theorem N25.Endgame.FBaseCoeffMap25_frobenius_iterate
    (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [CharP k p]
    (K : Type*) [Field K] [CharP K p] [Algebra k K]
    (n : ℕ) (hk : Nat.card k = p ^ n) (x : FBase k) :
    (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n) (FBaseCoeffMap25 k K x) =
      FBaseCoeffMap25 k K (x ^ Nat.card k) := by sorry
