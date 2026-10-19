-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_cyclotomicPowerCharacter_neg
-- name    : OAI.CirculantHadamard.cyclotomicPowerCharacter_neg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:18:11.236491+00:00
-- url     : https://prove2.me/theorems/a7244ead-2c1b-4571-9ad7-0ba03daac69f
-- title:
--   Conjugation inverts the cyclotomic character
-- statement:
--   Let $A$ be a commutative ring and $n>0$, and suppose $A[X]/(\Phi_n(X))$ is a domain of characteristic zero; let $\zeta$ be the class of $X$ and $\sigma$ the automorphism with $\sigma(\zeta)=\zeta^{n-1}$. For every $a\in\mathbb Z/n$,
--   $$
--   \zeta^{-a}=\sigma\bigl(\zeta^{a}\bigr),
--   $$
--   with exponents read in $\{0,\dots,n-1\}$.
--
--   The root-inverting conjugation acts on the cyclotomic character as $a\mapsto-a$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicIntegerEvaluation.lean#L50-L77

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation

open OAI OAI.CirculantHadamard
universe uA
open Polynomial
open scoped BigOperators
variable (A : Type uA) [CommRing A] (n : ℕ) [NeZero n]
variable (hn : 0 < n)
variable [IsDomain (AdjoinRoot (cyclotomic n A))]
variable [CharZero (AdjoinRoot (cyclotomic n A))]

theorem OAI.CirculantHadamard.cyclotomicPowerCharacter_neg (a : ZMod n) :
    CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
        (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd (-a)) =
      RamifiedConjugation.cyclotomicConjugation A n hn
        (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
          (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd a)) := by sorry
