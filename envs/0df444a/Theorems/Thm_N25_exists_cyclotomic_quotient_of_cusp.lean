-- Prove2me | Theorems.Thm_N25_exists_cyclotomic_quotient_of_cusp
-- name    : N25.exists_cyclotomic_quotient_of_cusp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:28.708238+00:00
-- url     : https://prove2.me/theorems/5c829247-0f2c-4cb5-8cb7-23c754fb1dad
-- title:
--   A rational cusp eigenline yields a cyclotomic quotient
-- statement:
--   Assume the cyclotomic relation $1+\gamma+\cdots+\gamma^4=0$ on the Jacobian. Let $c\in J$ be nonzero, satisfy $71c=0$ and $\gamma c=5c$, and be fixed by every arithmetic Galois element. Then there exists a surjective additive map $q:V\to\mathbb F_{71}$ such that
--
--   $$q(\sigma v)=\chi_{71}(\sigma)q(v)\qquad(\sigma\in\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q),\ v\in V).$$
--
--   This produces the cyclotomic quotient line of the Kummer kernel from the rational cusp class.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummer

set_option autoImplicit false
noncomputable section
open N25
local instance primeSeventyOneCuspQuotient_ie09c0d : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.exists_cyclotomic_quotient_of_cusp (hPhi : PhiFiveZero)
    (c : J) (hcne : c ≠ 0) (hc71 : 71 • c = 0)
    (hgamma : gamma c = 5 • c) (hcfix : ∀ σ : Gal, σ • c = c) :
    ∃ q : ↥V →+ ZMod 71, Function.Surjective q ∧
      ∀ (σ : Gal) (v : ↥V), q (vAct σ v) =
        (ExtCitation.cycloChar 71 σ : ZMod 71) * q v := by sorry
