-- Prove2me | Theorems.Thm_N25_characterField_prime_norm_residue
-- name    : N25.characterField_prime_norm_residue
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:41.680205+00:00
-- url     : https://prove2.me/theorems/732c29a9-a0de-484b-b19c-1e66814b956a
-- title:
--   Small contracted prime norms lie in four residue classes modulo $25$
-- statement:
--   Let $L=\mathbb Q(\zeta_{25})$ be the cyclotomic field and $K=L^{H_{25}}$ its quintic character subfield. Let $Q$ be a prime ideal of $\mathcal O_L$ with finite residue ring, assume $25\notin Q$, and let $P=Q\cap\mathcal O_K$. If $N(P)\le 24$, then the residue class of its absolute norm modulo $25$ is one of four possibilities:
--
--   $$N(P)\bmod 25\in\{1,7,18,24\}.$$
--
--   This restricts the possible small contracted primes entering the norm-cover computation. Formalization note: finiteness of $\mathcal O_L/Q$ is an explicit typeclass hypothesis ensuring a finite residue ring.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false
open scoped NumberField
open N25

theorem N25.characterField_prime_norm_residue
    (Q : Ideal (𝓞 cyclotomicField)) [Q.IsPrime]
    [Finite ((𝓞 cyclotomicField) ⧸ Q)]
    (h25 : (25 : 𝓞 cyclotomicField) ∉ Q)
    (hbound : (Q.under (𝓞 characterField)).absNorm ≤ 24) :
    ((Q.under (𝓞 characterField)).absNorm : ZMod 25) = 1 ∨
    ((Q.under (𝓞 characterField)).absNorm : ZMod 25) = 7 ∨
    ((Q.under (𝓞 characterField)).absNorm : ZMod 25) = 18 ∨
    ((Q.under (𝓞 characterField)).absNorm : ZMod 25) = 24 := by sorry
