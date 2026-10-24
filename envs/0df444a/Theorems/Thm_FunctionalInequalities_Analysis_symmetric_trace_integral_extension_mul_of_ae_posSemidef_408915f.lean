-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_trace_integral_extension_mul_of_ae_posSemidef_408915f
-- name    : FunctionalInequalities.Analysis.symmetric_trace_integral_extension_mul_of_ae_posSemidef_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:09.984751+00:00
-- url     : https://prove2.me/theorems/75a8f211-ef96-4976-94f8-ef56873fc3d0
-- title:
--   Extension of Trace Integral Bounds to Symmetric Matrices
-- statement:
--   This is the almost-everywhere positive-semidefinite extension step associated with Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $\iota$ be a finite index type with decidable equality, let $(\Omega,\nu)$ be an arbitrary measurable space with measure $\nu$, let $C\in\mathbb R$, and let $H:\Omega\to\operatorname{Matrix}(\iota,\iota,\mathbb R)$. Assume:
--
--   1. every entry of $H$ is measurable;
--   2. $H(x)$ is positive semidefinite for $\nu$-almost every $x$;
--   3. for every positive semidefinite matrix $A$, the function $x\mapsto\operatorname{tr}(AH(x)AH(x))$ is $\nu$-integrable and
--
--   $$
--   \int \operatorname{tr}(AH(x)AH(x))\,d\nu(x)
--   \le C\operatorname{tr}(A^2).
--   $$
--
--   Then every symmetric matrix $B$ has the same integrability and bound:
--
--   $$
--   \int \operatorname{tr}(BH(x)BH(x))\,d\nu(x)
--   \le C\operatorname{tr}(B^2).
--   $$
--
--   The theorem transfers a hypothesis stated only for positive semidefinite test matrices to all symmetric test matrices.
--
--   **Formalization Note** The coefficient $C$ has no sign assumption, $\nu$ need not be finite, and all positivity and almost-everywhere assertions use the stated matrix and measure-theoretic notions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Integral.lean#L29-L109 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Integral`, declaration `FunctionalInequalities.Analysis.symmetric_trace_integral_extension_mul_of_ae_posSemidef`; the repository is private at upload time).

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section
open Matrix MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.symmetric_trace_integral_extension_mul_of_ae_posSemidef_408915f
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {C : ℝ}
    (H : Ω → Matrix ι ι ℝ)
    (hH_meas : ∀ i j, Measurable (fun x => H x i j))
    (hH_psd : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hPSD : ∀ A : Matrix ι ι ℝ, A.PosSemidef →
      Integrable (fun x => (A * H x * A * H x).trace) ν ∧
        (∫ x, (A * H x * A * H x).trace ∂ν) ≤
          C * (A * A).trace)
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
    Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        C * (B * B).trace := by sorry
