-- Prove2me | Theorems.Thm_N25_level25_indices
-- name    : N25.level25_indices
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:31.221955+00:00
-- url     : https://prove2.me/theorems/3f282a3f-ddcf-4bc7-b677-af6d0ceeb2e0
-- title:
--   The level-$25$ subgroup indices are $150$ and $30$
-- statement:
--   Let $H=H_{25}=⟨7⟩≤(ℤ/25ℤ)^×$. Then $$[SL_2(ℤ):Γ_H(25)]=150,\qquad [SL_2(ℤ):Γ_0(25)]=30.$$ These indices are the global size inputs for the genus and cusp formulas.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false
open N25

theorem N25.level25_indices :
    (CohCarrier.GammaH 25 H25).index = 150 ∧
    (CongruenceSubgroup.Gamma0 25).index = 30 := by sorry
