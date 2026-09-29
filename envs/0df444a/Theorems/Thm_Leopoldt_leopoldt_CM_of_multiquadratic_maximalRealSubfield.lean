-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_CM_of_multiquadratic_maximalRealSubfield
-- name    : Leopoldt.leopoldt_CM_of_multiquadratic_maximalRealSubfield
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:32:33.080195+00:00
-- url     : https://prove2.me/theorems/275a9333-ba2e-45f3-85f6-0820b1735972
-- title:
--   Leopoldt's conjecture for CM fields with multiquadratic maximal real subfield
-- statement:
--   Let $K$ be a CM field whose maximal real subfield $K^+$ is multiquadratic over $\mathbb Q$. Equivalently, $K^+/\mathbb Q$ is Galois and every automorphism squares to the identity. Then Leopoldt’s conjecture holds for $K$ at every prime $p$. There is no need for $K/\mathbb Q$ itself to be Galois. The established multiquadratic theorem proves the conjecture for $K^+$; the established CM defect equivalence transfers it to $K$.
-- source:
--   Combination of platform theorems Leopoldt.leopoldtConjecture_iff_maximalRealSubfield and Leopoldt.leopoldt_totallyReal_multiquadratic; CM descent of Leopoldt defect in Preda Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1.1.

import Definitions.Def_LeopoldtDefect
open NumberField

namespace Leopoldt
theorem leopoldt_CM_of_multiquadratic_maximalRealSubfield (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCMField K]
    [IsGalois ℚ (maximalRealSubfield K)]
    (hG : ∀ σ : maximalRealSubfield K ≃ₐ[ℚ] maximalRealSubfield K, σ * σ = 1) :
    LeopoldtConjecture p K := by sorry
end Leopoldt
