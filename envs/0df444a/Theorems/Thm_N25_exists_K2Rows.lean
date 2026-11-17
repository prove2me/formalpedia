-- Prove2me | Theorems.Thm_N25_exists_K2Rows
-- name    : N25.exists_K2Rows
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:54.227149+00:00
-- url     : https://prove2.me/theorems/082e5698-d173-41e1-9e7d-02f41bc1c327
-- title:
--   The two cusp eigenlines produce the exact Kummer rows
-- statement:
--   Let $J$ be the geometric Jacobian, let $\gamma$ be its distinguished diamond action, let $V=\ker(\pi)$ be the selected Kummer kernel, and assume $1+\gamma+\gamma^2+\gamma^3+\gamma^4=0$ on $J$. Let $c,a\in J$ be nonzero $71$-torsion points such that $\gamma c=5c$, every Galois element fixes $c$, $\gamma a=57a$, and $\sigma a=\psi(\sigma)a$. Then there exist additive maps forming an exact character extension
--
--   $$0\longrightarrow\mathbb F_{71}^{\psi}\xrightarrow{i}V\xrightarrow{q}\mathbb F_{71}^{\chi_{71}}\longrightarrow0,$$
--
--    with $i$ injective, $q$ surjective, and both maps Galois equivariant for the displayed characters. This packages the cusp and Fricke eigenlines into the Kummer representation used in the endgame.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerPolynomial
import Definitions.Def_N25_GlobalKummer
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

set_option autoImplicit false
open N25

theorem N25.exists_K2Rows (hPhi : PhiFiveZero) (c a : J)
    (hcne : c ≠ 0) (hc71 : 71 • c = 0)
    (hcgamma : gamma c = 5 • c) (hcgal : ∀ σ : Gal, σ • c = c)
    (hane : a ≠ 0) (ha71 : 71 • a = 0)
    (hagamma : gamma a = 57 • a)
    (hagal : ∀ σ : Gal, σ • a = (psi σ : ZMod 71).val • a) : Nonempty K2Rows := by sorry
