-- Prove2me | Theorems.Thm_NestedLogitVariants_Competitive_lemma_3
-- name    : NestedLogitVariants.Competitive.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:22:24.792997+00:00
-- url     : https://prove2.me/theorems/22cf13fc-e0b2-4ace-afc2-c2ce48441f9a
-- title:
--   Lemma 3, p. 14 — removing a product with r_ij < γ_i Z + (1 − γ_i) R_i(S_i) strictly increases revenue
-- statement:
--   Assume $\gamma_i \le 1$ and $v_{i0} = 0$ for every nest $i \in M$, and $v_0 > 0$. Let $(S_1, \dots, S_m)$ be any assortment, with expected revenue $Z = \Pi(S_1, \dots, S_m)$. Suppose that in some nest $i$ the conditional revenue satisfies $R_i(S_i) \ge Z$, and that some product $j \in S_i$ has a small revenue:
--
--   $$r_{ij} < \gamma_i\, Z + (1 - \gamma_i)\, R_i(S_i).$$
--
--   Then removing product $j$ from $S_i$ yields an assortment $(S_1, \dots, S_{i-1}, S_i \setminus \{j\}, S_{i+1}, \dots, S_m)$ whose expected revenue is strictly larger than $Z$.
--
--   The lemma provides the mechanism by which products with small revenues are removed from an assortment without loss; combined with Proposition 2 it gives the revenue threshold satisfied by every product of an optimal assortment.
--
--   **Formalization Note** The standing assumptions of §3 (p. 13), $\gamma_i \le 1$ and $v_{i0} = 0$ for every nest, are hypotheses, together with those of §1 and the disclosed pins of the model definition ($v_{ij} > 0$, $r_{ij} \ge 0$, $\gamma_i > 0$, revenues ordered within each nest). The positivity $v_0 > 0$ is the section's own "without loss of generality" assumption (p. 14), stated as a hypothesis here because the argument uses it.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 14, Lemma 3

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

namespace NestedLogitVariants.Competitive

/-- Lemma 3, p. 14: if `Z = Π(S_1, …, S_m)` and a product `j ∈ S_i` satisfies
`r_ij < γ_i Z + (1 − γ_i) R_i(S_i)` and `R_i(S_i) ≥ Z`, then removing `j` from `S_i` yields a
strictly larger expected revenue than `Z`. -/
theorem lemma_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (S : ι → Finset (Fin n)) (i : ι) (j : Fin n) (hj : j ∈ S i)
    (hr : I.r i j < I.γ i * revenue I S + (1 - I.γ i) * R I i (S i))
    (hR : revenue I S ≤ R I i (S i)) :
    revenue I S < revenue I (Function.update S i ((S i).erase j)) := by sorry

end NestedLogitVariants.Competitive
