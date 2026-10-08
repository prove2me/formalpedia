-- Prove2me | Theorems.Thm_NestedLogitVariants_Competitive_revenue_threshold_of_optimal
-- name    : NestedLogitVariants.Competitive.revenue_threshold_of_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:22:48.751743+00:00
-- url     : https://prove2.me/theorems/c627cad9-d8f6-44df-8050-dc837f5b40ff
-- title:
--   §3, p. 15 — every product j ∈ S_i* of an optimal assortment has r_ij ≥ γ_i Z* + (1 − γ_i) R_i(S_i*)
-- statement:
--   Assume $\gamma_i \le 1$ and $v_{i0} = 0$ for every nest $i \in M$, and $v_0 > 0$. Let $(S^*_1, \dots, S^*_m)$ be an optimal solution to the assortment problem (2), with optimal expected revenue $Z^*$. Then every product $j$ offered in nest $i$, $j \in S^*_i$, satisfies
--
--   $$r_{ij} \ge \gamma_i\, Z^* + (1 - \gamma_i)\, R_i(S^*_i).$$
--
--   This is the "useful implication of Proposition 2 and Lemma 3" observed after Lemma 3: if some offered product violated the threshold, it could be removed for a strictly larger revenue. It is the inequality the proof of Theorem 4 uses for the product $j$ that is exchanged.
--
--   **Formalization Note** The standing assumptions of §3 (p. 13), $\gamma_i \le 1$ and $v_{i0} = 0$ for every nest, are hypotheses, together with those of §1 and the disclosed pins of the model definition ($v_{ij} > 0$, $r_{ij} \ge 0$, $\gamma_i > 0$, revenues ordered within each nest). The positivity $v_0 > 0$ is the section's own "without loss of generality" assumption (p. 14), stated as a hypothesis here because the argument uses it.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 15, paragraph after the proof of Lemma 3

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

namespace NestedLogitVariants.Competitive

/-- The observation after Lemma 3, p. 15: if `(S*_1, …, S*_m)` is optimal for problem (2),
then `r_ij ≥ γ_i Z* + (1 − γ_i) R_i(S*_i)` for every `j ∈ S*_i`. -/
theorem revenue_threshold_of_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal I Sstar)
    (i : ι) (j : Fin n) (hj : j ∈ Sstar i) :
    I.γ i * revenue I Sstar + (1 - I.γ i) * R I i (Sstar i) ≤ I.r i j := by sorry

end NestedLogitVariants.Competitive
