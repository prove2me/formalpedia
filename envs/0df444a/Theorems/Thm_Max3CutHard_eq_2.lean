-- Prove2me | Theorems.Thm_Max3CutHard_eq_2
-- name    : Max3CutHard.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:36.157649+00:00
-- url     : https://prove2.me/theorems/9abae8d0-2132-406b-81e4-2c79bf1026b3
-- title:
--   Eq. (2) — soundness of the gadget reduction
-- statement:
--   Let $(I_0,I_1,I_2)$ be a family of gadgets with non-negative weights and $\Phi$ a role-separated instance with weights $\lambda_e\ge0$ summing to $1$. For every colouring $\chi$ of $J(\Phi)$, with $y=\chi(g_0,\dots,g_{k-1})$ the colours of the globals,
--
--   $$\mathrm{cut}_\chi(J)\ \le\ \sum_e\lambda_e\,V_{t_e}\big(\chi(u_e),\chi(w_e),\chi(w'_e),y\big).$$
--
--   The bound holds because the auxiliary vertices of different copies are disjoint.
--
--   Differences from the source:
--   - generalization: after normalising y ∈ Y_k (colourings whose globals form a restricted growth string); k ≥ 3 → every colouring χ and the actual colours y of the globals; every k; reason: the source's normalisation permutes colours, which changes no cut value, and calls it only a computational saving; the normalised colourings are a special case
--   - encoding: sum over the equations e → sum over the positions i of the list of equations; reason: Lean convention; same sum
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, The reduction, Eq. (2), p.5

import Mathlib
import Definitions.Def_Max3CutHard_J
import Definitions.Def_Max3CutHard_cutR
import Definitions.Def_Max3CutHard_Gadget_gval
import Definitions.Def_Max3CutHard_IsNonneg
import Definitions.Def_Max3CutHard_WInst_IsWeighting

namespace Max3CutHard

/-- **Eq. (2): soundness of the reduction.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, The reduction, Eq. (2), p.5: "For
every colouring `χ` of `J`, after normalising `y = χ(g0, …, g(k−1)) ∈ Y_k`,
`cut_χ(J) ≤ Σ_e λ_e V_{t_e}(χ(u_e), χ(w_e), χ(w′_e), y)`, (2) since the auxiliary vertices of
different copies are disjoint."

**Formalization Note.** Stated for every colouring `χ`, with `y` the actual colours of the globals
(no normalisation `y ∈ Y_k`); every `k`, every family of non-negatively weighted gadgets and
every weighted instance. The sum runs over the listed equations `i` with weights `λ_i`. -/
theorem eq_2 {U W : Type} {k : ℕ} [NeZero k] (F : Family k) (hF : ∀ t, IsNonneg (F t).edges)
    (Φ : WInst U W) (hΦ : Φ.IsWeighting) (χ : JVert Φ F → Fin k) :
    cutR χ (J Φ F) ≤ ∑ i : Fin Φ.eqs.length, (Φ.eqs.get i).2 *
      (F (Φ.eqs.get i).1.t).gval
        ![χ (Sum.inl (Φ.eqs.get i).1.u), χ (Sum.inr (Sum.inl (Φ.eqs.get i).1.w)),
          χ (Sum.inr (Sum.inl (Φ.eqs.get i).1.w'))]
        (fun g => χ (Sum.inr (Sum.inr (Sum.inl g)))) := by sorry

end Max3CutHard
