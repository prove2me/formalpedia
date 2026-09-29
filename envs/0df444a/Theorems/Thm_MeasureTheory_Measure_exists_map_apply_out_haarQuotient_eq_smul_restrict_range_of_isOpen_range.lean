-- Prove2me | Theorems.Thm_MeasureTheory_Measure_exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range
-- name    : MeasureTheory.Measure.exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/9f455fce-e807-5050-9db0-3b56fd19d6c0
-- title:
--   Weil's formula: pushforward of quotient Haar measure along open-range f
-- statement:
--   Let $G$ be a commutative locally compact second countable topological group and $H$ a commutative locally compact Hausdorff topological group, both equipped with their Borel $\sigma$-algebras, let $\mu$ be a Haar measure on $G$ and $\nu$ a Haar measure on $H$. Let $f : G \to H$ be a continuous group homomorphism whose range is open, let $N$ be a subgroup of $G$ whose elements are exactly the $x \in G$ with $f(x) = 1$, and let $\mu_N$ be a Haar measure on $N$. Write $\mathrm{HaarQuotient.measure}\ \mu\ N\ \mu_N$ for the measure on the quotient of $G$ by the orbit relation of the multiplication action of $N$ obtained by pushing forward, along the quotient map, the measure $\mu$ weighted by the density $g \mapsto \mathrm{weight}\ N\ \mu_N\ g \big/ \int^-_{x : N} \mathrm{weight}\ N\ \mu_N\ (x g)\, d\mu_N$. Then there exists a real $\kappa > 0$ such that the pushforward of this quotient measure along $q \mapsto f(q.\mathrm{out})$, where $q.\mathrm{out}$ is a chosen representative of the class $q$, equals $\mathrm{ENNReal.ofReal}\ \kappa$ times the restriction of $\nu$ to the range of $f$.
--
--   This is Weil's formula in quotient form: the induced map from $N \backslash G$ to the open subgroup $f(G)$ transports the quotient Haar measure to a Haar measure on $f(G)$, hence to a positive multiple of $\nu|_{f(G)}$. It is used in the comparison of Haar integrals on idele class groups and on unit groups, via [`NumberField.exists_pos_forall_lintegral_comp_idelicNorm_haarQuotient_ker_eq_mul_setLIntegral_range`](thm.html#NumberField.exists_pos_forall_lintegral_comp_idelicNorm_haarQuotient_ker_eq_mul_setLIntegral_range) and [`AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq`](thm.html#AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range.lean

import Mathlib
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

theorem MeasureTheory.Measure.exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (f : G →* H) (hf : Continuous f) (hopen : IsOpen (Set.range f))
    (N : Subgroup G) (hN : ∀ x : G, x ∈ N ↔ f x = 1)
    (μN : Measure N) [μN.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map (fun q : MulAction.orbitRel.Quotient N G => f q.out) (HaarQuotient.measure μ N μN) =
        ENNReal.ofReal κ • ν.restrict (Set.range f) := by sorry
