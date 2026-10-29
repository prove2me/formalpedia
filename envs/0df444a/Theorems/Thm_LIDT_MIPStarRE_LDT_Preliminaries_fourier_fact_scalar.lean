-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_fourier_fact_scalar
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.fourier_fact_scalar
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:19:01.541783+00:00
-- url     : https://prove2.me/theorems/79fae647-16c7-4154-ba73-b419ab2af55d
-- title:
--   Fourier Fact Scalar
-- statement:
--   **A finite-field additive character averages to zero away from the zero coefficient.**
--
--   For a finite-field element `a`, average the scalar Fourier character at the product `x * a` over uniformly sampled `x`. The result is one at zero frequency and zero otherwise:
--
--   $$
--   \mathbb E_{x\in F}\,\operatorname{ffChar}(x a)
--   =\begin{cases}1,&a=0,\\0,&a\ne0.\end{cases}
--   $$
--
--   The values are viewed in the complex numbers. This is the scalar orthogonality fact used as a top-level finite-field input for polynomial and QPBT estimates.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.fourier_fact_scalar`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/FiniteFields.lean#L117-L141

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_FiniteFields
import Mathlib
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

open LIDT
/-!
# Finite fields and Fourier orthogonality

This file formalizes the finite-field trace and the two Fourier orthogonality facts
from `references/ldt-paper/preliminaries.tex` (lines 15–83).

## Main results

* `fourier_fact_scalar` (`prop:fourier-fact-scalar`):
  `𝔼_{x ∈ 𝔽_q} ω^{tr[x·a]} = 1 if a = 0, 0 otherwise`
* `fourier_fact_vector` (`prop:fourier-fact-vector`):
  Vector version over `𝔽_q^m`.

## References

* `references/ldt-paper/preliminaries.tex`, lines 15–83
-/

@[expose] public section

open scoped BigOperators

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT



-- The Fourier section uses `[Fintype F]` (rather than `[Finite F]` as in the Trace section)
-- because `AddChar.expect_eq_ite` requires a `Fintype` instance. Downstream users with
-- only `[Finite F]` can obtain `Fintype` via `Fintype.ofFinite`.
variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

theorem LIDT.MIPStarRE.LDT.Preliminaries.fourier_fact_scalar (a : F) :
    𝔼 x : F, _root_.LIDT.MIPStarRE.LDT.Preliminaries.ffChar (p := p) (F := F) (x * a) =
      if a = 0 then (1 : ℂ) else 0 := by sorry
