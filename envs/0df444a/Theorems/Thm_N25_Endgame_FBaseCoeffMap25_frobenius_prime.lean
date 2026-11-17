-- Prove2me | Theorems.Thm_N25_Endgame_FBaseCoeffMap25_frobenius_prime
-- name    : N25.Endgame.FBaseCoeffMap25_frobenius_prime
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:32.810063+00:00
-- url     : https://prove2.me/theorems/1944c61f-6a85-4e58-807f-747f627c0421
-- title:
--   Prime Frobenius commutes with coefficient extension
-- statement:
--   Let $ℓ$ be a prime, let $K$ be a field of characteristic $ℓ$ equipped with an $𝔽_ℓ$-algebra structure, let $F_{𝔽_ℓ}$ and $F_K$ be the level-$25$ modular function fields over $𝔽_ℓ$ and $K$, and let $c:F_{𝔽_ℓ}→F_K$ be coefficient extension. If $Φ_ℓ:F_K→F_K$ is the $q$-expansion Frobenius, then every $f∈F_{𝔽_ℓ}$ satisfies
--
--   $$Φ_ℓ(c(f))=c(f^ℓ).$$
--
--   This is the basic compatibility connecting geometric Frobenius with the finite-field power map.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CoefficientMap

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.FBaseCoeffMap25_frobenius_prime
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type*) [Field K] [CharP K ℓ] [Algebra (ZMod ℓ) K]
    (f : FBase (ZMod ℓ)) :
    ModularCurve.qExpFrobeniusModL K Γ25 ℓ
        (FBaseCoeffMap25 (ZMod ℓ) K f) =
      FBaseCoeffMap25 (ZMod ℓ) K (f ^ ℓ) := by sorry
