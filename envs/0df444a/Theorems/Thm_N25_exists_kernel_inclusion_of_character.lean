-- Prove2me | Theorems.Thm_N25_exists_kernel_inclusion_of_character
-- name    : N25.exists_kernel_inclusion_of_character
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:13.956033+00:00
-- url     : https://prove2.me/theorems/144126e8-63cb-4d00-a850-623ed0f6f6ee
-- title:
--   A character eigenvector embeds the $\psi$-line into the Kummer kernel
-- statement:
--   Assume $1+\gamma+\cdots+\gamma^4=0$ on the Jacobian. Let $a\in J$ be nonzero, satisfy $71a=0$ and $\gamma a=57a$, and transform by $\sigma a=\psi(\sigma)a$. Then there exists an injective additive map $i:\mathbb F_{71}\to V$ such that
--
--   $$i(1)=a\quad\text{in }J,\qquad \sigma i(t)=i(\psi(\sigma)t).$$
--
--   This realizes the $\psi$-eigenline as the kernel line in the Kummer extension.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummer

set_option autoImplicit false
noncomputable section
open N25
local instance prime71_N25_exists_kernel_inclusion_of_character_idf1557 : Fact (Nat.Prime 71) :=
  ⟨by decide⟩

theorem N25.exists_kernel_inclusion_of_character (hPhi : PhiFiveZero)
    (a : J) (ha : a ≠ 0) (ha71 : 71 • a = 0)
    (hgamma : gamma a = 57 • a)
    (hgal : ∀ σ : Gal, σ • a = (psi σ : ZMod 71).val • a) :
    ∃ i : ZMod 71 →+ ↥V, Function.Injective i ∧ (i 1 : J) = a ∧
      ∀ (σ : Gal) (t : ZMod 71), vAct σ (i t) = i ((psi σ : ZMod 71) * t) := by sorry
