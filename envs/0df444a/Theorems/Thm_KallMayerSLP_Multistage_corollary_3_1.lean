-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_corollary_3_1
-- name    : KallMayerSLP.Multistage.corollary_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:20:58.441249+00:00
-- url     : https://prove2.me/theorems/f2854740-5416-4d61-988f-43500fff1987
-- title:
--   Corollary 3.1 — successive splitting converges to a value $V^*\le\hat V$
-- statement:
--   Let $\hat V$ be the optimal value of problem (3.10), and let Assumption 3.2 hold. Then each method splitting successively any nodes (except the root) in the scenario tree according to the cut and paste procedure converges to a value $V^*\le\hat V$: if $\mathcal T_0,\mathcal T_1,\dots$ are scenario trees, each obtained from the previous one by one cut and paste step, then the optimal values $V_k$ of the aggregated problems converge to a limit $V^*$, and
--   $$
--   V^*\le\hat V.
--   $$
--
--   **Formalization Note** Convergence is in the extended reals. The book leaves open whether $V^*<\hat V$ can occur.
--
--   Differences from the source:
--   - reading: Assumption 3.2: the A_tt complete fixed recourse matrices ∀t → complete recourse of A_tt for t = 2, …, T; reason: A_11 is not a recourse matrix, and the book's Example 3.1 calls a problem with a non-complete first stage complete fixed recourse; this is the weaker hypothesis, so the statement implies the ∀t one
--   - generalization: supp ℙ_{ξ_t} ⊆ Ξ^t → ξ_t ∈ Ξ^t almost surely; reason: the support inclusion implies the almost sure one, and they agree for closed Ξ^t, so the statement specializes to the source
--   - encoding: each method splitting successively any nodes → an arbitrary sequence of scenario trees, each one cut and paste step from the previous; reason: a method generates such a sequence
--   - encoding: min → infimum in EReal; reason: +∞ on infeasible and -∞ on unbounded problems; the book assumes neither case away
--   - generalization: a partition of Ξ^{ν+1} into subintervals, |C_n| = r_n ≥ 1 → ScenarioTree, whose cells may be empty (a node may then have no child when Ξ^{ν+1} is empty); reason: every tree of p.261 is a ScenarioTree, so the statement specializes to the book's trees
--   - encoding: ξ̄^n_t = 𝔼[ξ_t | ξ_t ∈ Ξ^t_n], undefined on a P-null cell → xiBar = 0 on a P-null cell (Lean's 0⁻¹ = 0); reason: such a node and its descendants have p_n = 0, and their constraints are solvable by complete recourse of A_tt (t ≥ 2), so no value of (3.14) depends on the choice
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Corollary 3.1, p.270 (PDF 279)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_value
import Definitions.Def_KallMayerSLP_Multistage_aggValue
import Definitions.Def_KallMayerSLP_Multistage_IsCutAndPaste

namespace KallMayerSLP.Multistage

open MeasureTheory Filter Topology

/-- **Chapter 3, Corollary 3.1** (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3,
Corollary 3.1, p.270, PDF 279): "Let `V̂` be the optimal value of problem (3.10). If Assumption 3.2 is
satisfied, then each method, splitting succesively any nodes (except the root) in the scenario tree
according to the cut and paste procedure, converges to a value `V* ≤ V̂`."

**Formalization Note.** A method is a sequence of scenario trees `𝒯s k`, each obtained from the
previous one by one cut and paste step, on an arbitrary node of a stage `≥ 2`. Convergence is in
`EReal`. -/
theorem corollary_3_1 {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) (𝒯s : ℕ → ScenarioTree D Ξ)
    (hstep : ∀ k, ∃ (s : ℕ) (i : (𝒯s k).Node s) (i₁ i₂ : (𝒯s (k + 1)).Node s)
      (φ : ∀ t, (𝒯s (k + 1)).Node t → (𝒯s k).Node t), IsCutAndPaste (𝒯s k) (𝒯s (k + 1)) i i₁ i₂ φ) :
    ∃ Vstar : EReal,
      Tendsto (fun k => aggValue (𝒯s k) P ξ) atTop (𝓝 Vstar) ∧ Vstar ≤ value D P ξ := by sorry

end KallMayerSLP.Multistage
