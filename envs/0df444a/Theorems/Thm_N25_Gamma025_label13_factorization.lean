-- Prove2me | Theorems.Thm_N25_Gamma025_label13_factorization
-- name    : N25.Gamma025_label13_factorization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:00.876519+00:00
-- url     : https://prove2.me/theorems/89032f0e-6056-4d75-a079-19e485a5b743
-- title:
--   Five label-$13$ powers represent $\Gamma_0(25)/\Gamma_H(25)$
-- statement:
--   Let $H=\langle7\rangle=\{1,7,18,24\}\subset(\mathbf Z/25\mathbf Z)^\times$, and let $\Gamma_H(25)\subset\Gamma_0(25)$ be the subgroup whose lower-right residue lies in $H$. Let $T\in\Gamma_0(25)$ have lower-right unit label $13^{-1}$ modulo $25$. Then every $B\in\Gamma_0(25)$ admits a factorization
--
--   $$B=C T^k\quad\text{for some }k\in\{0,1,2,3,4\}\text{ and }C\in\Gamma_H(25).$$
--
--   This supplies the five coset representatives used to pass from level $\Gamma_0(25)$ to level $\Gamma_H(25)$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25

set_option autoImplicit false
open CongruenceSubgroup
open N25

theorem N25.Gamma025_label13_factorization (T : Gamma0 25)
    (hT : CohCarrier.gamma0Units 25 T = (ZMod.unitOfCoprime 13 (by decide))⁻¹)
    (B : Gamma0 25) :
    ∃ k : Fin 5, ∃ C : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      C ∈ CohCarrier.GammaH 25 N25.H25 ∧
        (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
          C * (T : Matrix.SpecialLinearGroup (Fin 2) ℤ) ^ k.val := by sorry
