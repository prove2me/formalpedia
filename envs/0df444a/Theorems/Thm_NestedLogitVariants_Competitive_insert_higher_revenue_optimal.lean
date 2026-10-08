-- Prove2me | Theorems.Thm_NestedLogitVariants_Competitive_insert_higher_revenue_optimal
-- name    : NestedLogitVariants.Competitive.insert_higher_revenue_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:23:00.899255+00:00
-- url     : https://prove2.me/theorems/8d65ac13-ac1f-48d3-b4b5-632543c572ff
-- title:
--   Proof of Theorem 4, p. 15 — adding a missing higher-revenue product k < j to S_i* keeps the assortment optimal
-- statement:
--   Assume $\gamma_i \le 1$ and $v_{i0} = 0$ for every nest $i \in M$, and $v_0 > 0$. Let $(S^*_1, \dots, S^*_m)$ be an optimal solution to the assortment problem (2), and suppose that in some nest $i$ the assortment $S^*_i$ contains product $j$ but not product $k$, where $k < j$ (so $r_{ik} \ge r_{ij}$). Let $\hat S_i = S^*_i \cup \{k\}$. Then
--
--   $$(S^*_1, \dots, S^*_{i-1}, \hat S_i, S^*_{i+1}, \dots, S^*_m)$$
--
--   is also an optimal solution to problem (2).
--
--   This exchange step is the core of the proof of Theorem 4: repeating it fills every gap in every nest until each nest offers a set of the form $\{1, 2, \dots, j\}$.
--
--   **Formalization Note** The standing assumptions of §3 (p. 13), $\gamma_i \le 1$ and $v_{i0} = 0$ for every nest, are hypotheses, together with those of §1 and the disclosed pins of the model definition ($v_{ij} > 0$, $r_{ij} \ge 0$, $\gamma_i > 0$, revenues ordered within each nest). The positivity $v_0 > 0$ is the section's own "without loss of generality" assumption (p. 14), stated as a hypothesis here because the argument uses it. Products are indexed $0, \dots, n-1$; $k < j$ compares indices, which by the ordering of revenues means $r_{ik} \ge r_{ij}$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 15, proof of Theorem 4 (first paragraph)

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

namespace NestedLogitVariants.Competitive

/-- Proof of Theorem 4, p. 15 (exchange step): if `(S*_1, …, S*_m)` is optimal and `S*_i`
contains product `j` but not product `k` with `k < j`, then adding `k` to `S*_i` gives an
assortment that is also optimal. -/
theorem insert_higher_revenue_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal I Sstar)
    (i : ι) (j k : Fin n) (hj : j ∈ Sstar i) (hk : k ∉ Sstar i) (hkj : k < j) :
    IsOptimal I (Function.update Sstar i (insert k (Sstar i))) := by sorry

end NestedLogitVariants.Competitive
