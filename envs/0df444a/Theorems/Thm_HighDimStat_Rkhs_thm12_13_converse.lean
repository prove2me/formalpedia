-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_thm12_13_converse
-- name    : HighDimStat.Rkhs.thm12_13_converse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:27:59.161424+00:00
-- url     : https://prove2.me/theorems/ce4affaf-74d0-4174-82b1-0325c0dbea81
-- title:
--   Every Hilbert space of functions with bounded evaluations has a reproducing kernel (Theorem 12.13)
-- statement:
--   **Theorem 12.13.** The converse of Theorem 12.11, completing the Moore-Aronszajn
--   equivalence: a Hilbert space of functions is a reproducing kernel Hilbert space (in the
--   Definition 12.12 sense) if and only if it arises from some PSD kernel via Theorem 12.11.
--
--   Given any Hilbert space $H$ of real-valued functions on $X$ (embedded via an injective
--   linear map into $X\to\mathbb R$) in which the evaluation functionals are all bounded
--   (Definition 12.12), there is a unique positive semidefinite kernel $K$ that satisfies the
--   reproducing property (12.3) for $H$.
--
--   The proof constructs $K$ directly from the Riesz representers $R_x$ of each evaluation
--   functional (Theorem 12.5), via $K(x,z):=\langle R_x,R_z\rangle_H$, and identifies
--   $K(\cdot,x)$ with $R_x$ itself.
--
--   **Formalization Note** `htoFun : Function.Injective toFun` is added explicitly as a
--   hypothesis, since Definition 12.12's "Hilbert space of real-valued functions on $X$"
--   already presupposes each element of $H$ corresponds to a genuine, distinguishable
--   function (the injectivity `IsRKHS` itself later asserts of the constructed kernel's own
--   embedding); it is not additional content beyond what "of functions" already means, and it
--   matches the book's informal but load-bearing framing. Uniqueness is of $K$ itself (an
--   ordinary function $X\times X\to\mathbb R$), not of a further Hilbert space, so `∃!` applies
--   directly without the isometry apparatus Theorem 12.11's uniqueness needs.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 391 (PDF p. 411), Theorem 12.13, Definition 12.12

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 12.13 (p. 391): given any Hilbert space `H` of real-valued functions on `X`
(embedded via the injective linear map `toFun`, Definition 12.12's "Hilbert space of
functions") in which the evaluation functionals are all bounded, there is a unique PSD
kernel `K` that satisfies the reproducing property (12.3) for `H`, via some feature map. -/
theorem thm12_13_converse (toFun : H →ₗ[ℝ] (X → ℝ)) (htoFun : Function.Injective toFun)
    (hEval : HasBoundedEvalFunctionals toFun) :
    ∃! K : X → X → ℝ, IsPSDKernel K ∧ ∃ feature : X → H, IsRKHS K toFun feature := by sorry

end HighDimStat.Rkhs
