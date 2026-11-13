-- Prove2me | Theorems.Thm_OddOrder_RepresentationTheory_cfdot_real_vchar_even
-- name    : OddOrder.RepresentationTheory.cfdot_real_vchar_even
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T06:19:37.582737+00:00
-- url     : https://prove2.me/theorems/27582684-8ca2-48ca-97da-a912883ad669
-- title:
--   Peterfalvi (7.9): parity of $\langle\varphi,\psi\rangle$ for real virtual characters of odd-order groups
-- statement:
--   Let $G$ be a finite group of odd order, and let $\varphi,\psi\in\mathbb Z[\mathrm{Irr}(G)]$ (`ZIrr G`) be real virtual characters (`ClassFunction.IsReal`). Then there exist integers $m,a,b$ with
--   $$m=\langle\varphi,\psi\rangle,\qquad a=\langle\varphi,1_G\rangle,\qquad b=\langle\psi,1_G\rangle,\qquad m-ab\ \text{ even}.$$
--   So $\langle\varphi,\psi\rangle\equiv\langle\varphi,1_G\rangle\langle\psi,1_G\rangle\pmod 2$.
--
--   This is the parity primitive used in Peterfalvi (7.9): by the Fourier expansion in $\mathrm{Irr}(G)$, the terms are paired by $\chi\mapsto\bar\chi$, whose only fixed point is $1_G$ when $|G|$ is odd.
--
--   **Formalization Note.** The statement is bundled: the integers are returned together with equations to the complex inner products. $G$ carries `Fintype` and `Invertible (Nat.card G : ℂ)` instances.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_ParityPrimitive.lean#L137-L189

import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Finite G]

section Main

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in

theorem cfdot_real_vchar_even (hodd : Odd (Nat.card G))
    {φ ψ : ClassFunction G ℂ} (hφZ : φ ∈ ZIrr G) (hφR : ClassFunction.IsReal φ)
    (hψZ : ψ ∈ ZIrr G) (hψR : ClassFunction.IsReal ψ) :
    ∃ m a b : ℤ, (m : ℂ) = ClassFunction.inner φ ψ ∧
      (a : ℂ) = ClassFunction.inner φ (trivialIrreducibleCharacter G : ClassFunction G ℂ) ∧
      (b : ℂ) = ClassFunction.inner ψ (trivialIrreducibleCharacter G : ClassFunction G ℂ) ∧
      Even (m - a * b) := by sorry

end Main

end OddOrder.RepresentationTheory
