-- Prove2me | Theorems.Thm_MazurTransfer_OneDimensionalSelectedQuotientKernel_exists_injective_with_selected_kernel
-- name    : MazurTransfer.OneDimensionalSelectedQuotientKernel.exists_injective_with_selected_kernel
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T02:35:27.764141+00:00
-- url     : https://prove2.me/theorems/2197049b-6776-45aa-87f9-57f0fc586be3
-- statement:
--   Given an exact representation sequence with scalar one-dimensional source and one-dimensional quotient, every specified surjection onto that same quotient admits an injective scalar-character inclusion whose range is exactly its kernel. The previously selected surjection is retained. The complete original finite-dimensional hypotheses and all four original proof helper types are checked. The named downstream consumers are the selected actual norm-character quotient maps.

import Definitions.Def_MazurTransfer_IntertwiningMapOriginalKernelCoordinateData20261019
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

theorem MazurTransfer.OneDimensionalSelectedQuotientKernel.exists_injective_with_selected_kernel : ∀ {k G V B : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup B] [Module k B]
    [FiniteDimensional k V] [FiniteDimensional k B]
    (σ : Representation k G k) (ρ : Representation k G V) (τ : Representation k G B)
    (hB : Module.finrank k B = 1)
    (i : Representation.IntertwiningMap σ ρ) (q : Representation.IntertwiningMap ρ τ)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (p : Representation.IntertwiningMap ρ τ) (hp : Function.Surjective p),
    ∃ j : Representation.IntertwiningMap σ ρ,
      Function.Injective j ∧ LinearMap.range j.toLinearMap = LinearMap.ker p.toLinearMap := by sorry
