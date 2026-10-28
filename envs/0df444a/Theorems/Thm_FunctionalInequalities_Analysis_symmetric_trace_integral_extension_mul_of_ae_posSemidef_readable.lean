-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_trace_integral_extension_mul_of_ae_posSemidef_readable
-- name    : FunctionalInequalities.Analysis.symmetric_trace_integral_extension_mul_of_ae_posSemidef_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:04.312918+00:00
-- url     : https://prove2.me/theorems/bb367c0f-60b7-46e5-bbe8-0f5d9f6169fc
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem symmetric_trace_integral_extension_mul_of_ae_posSemidef
--       {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {C : ℝ}
--       (H : Ω → Matrix ι ι ℝ)
--       (hH_meas : ∀ i j, Measurable (fun x => H x i j))
--       (hH_psd : ∀ᵐ x ∂ν, (H x).PosSemidef)
--       (hPSD : ∀ A : Matrix ι ι ℝ, A.PosSemidef →
--         Integrable (fun x => (A * H x * A * H x).trace) ν ∧
--           (∫ x, (A * H x * A * H x).trace ∂ν) ≤
--             C * (A * A).trace)
--       {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
--       Integrable (fun x => (B * H x * B * H x).trace) ν ∧
--         (∫ x, (B * H x * B * H x).trace ∂ν) ≤
--           C * (B * B).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Integral`](https://prove2.me/theorems/09aa8c12-3230-447e-89a1-dc642659f2aa).
--
--   Supporting theorems: [`jordan_trace_domination`](https://prove2.me/theorems/a6423829-e14f-4879-bca7-f5ac02b2f042), [`symmetric_jordan_decomposition`](https://prove2.me/theorems/a088e571-4bf9-4eb8-9d83-6d45e8be135b), [`trace_energy_nonneg`](https://prove2.me/theorems/1ddd2a2c-ff85-499e-a245-832c9fd056bb).
--
--   Next: [`integral_trace_mul_of_mean_one`](https://prove2.me/theorems/0fa1db57-6ad5-4665-9a1e-3a5d91a7bc2b).
--
--   [Source excerpt, lines 32–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Integral.lean#L32-L44) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Integral.lean#L29-L109 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Integral`, declaration `FunctionalInequalities.Analysis.symmetric_trace_integral_extension_mul_of_ae_posSemidef`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Integral

open Matrix MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.symmetric_trace_integral_extension_mul_of_ae_posSemidef_readable
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
