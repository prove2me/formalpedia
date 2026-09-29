-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_CM_of_biquadratic_maximalRealSubfield
-- name    : Leopoldt.leopoldt_CM_of_biquadratic_maximalRealSubfield
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:28:29.958588+00:00
-- url     : https://prove2.me/theorems/23857191-3c8f-4ccd-8856-2d5b8daf6ed6
-- title:
--   Leopoldt's conjecture for CM fields with a biquadratic maximal real subfield
-- statement:
--   Let $K$ be a CM number field whose maximal totally real subfield $K^+$ is a biquadratic extension of $\mathbb Q$: it is Galois of degree four and every automorphism has order at most two. Then Leopoldt’s conjecture holds for $K$ at every prime $p$, including $2$. This applies to certain non-Galois CM fields of degree eight, as well as abelian examples. The conjecture for a CM field is equivalent to that for its maximal real subfield, where the proved biquadratic case applies.
-- source:
--   Direct consequence of the platform theorems Leopoldt.leopoldtConjecture_iff_maximalRealSubfield and Leopoldt.leopoldt_totallyReal_biquadratic; CM descent of Leopoldt defect follows the basic setup of Preda Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1.1.

import Definitions.Def_LeopoldtDefect
open NumberField

namespace Leopoldt
theorem leopoldt_CM_of_biquadratic_maximalRealSubfield (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCMField K]
    [IsGalois ℚ (maximalRealSubfield K)]
    (hK : Module.finrank ℚ (maximalRealSubfield K) = 4)
    (hG : ∀ σ : maximalRealSubfield K ≃ₐ[ℚ] maximalRealSubfield K, σ * σ = 1) :
    LeopoldtConjecture p K := by sorry
end Leopoldt
