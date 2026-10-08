-- Prove2me | Theorems.Thm_NestedLogitVariants_Competitive_proposition_2
-- name    : NestedLogitVariants.Competitive.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:22:31.613984+00:00
-- url     : https://prove2.me/theorems/557491b1-91ed-495f-835f-57e45b414b4e
-- title:
--   Proposition 2, p. 14 — a nonempty nest of an optimal assortment earns R_i(S_i*) ≥ Z*
-- statement:
--   Assume $\gamma_i \le 1$ and $v_{i0} = 0$ for every nest $i \in M$, and $v_0 > 0$. Let $(S^*_1, \dots, S^*_m)$ be an optimal solution to the assortment problem (2), with optimal expected revenue $Z^* = \Pi(S^*_1, \dots, S^*_m)$. If the assortment $S^*_i$ offered in nest $i$ is nonempty, then the expected revenue obtained from nest $i$, conditional on a customer choosing it, is at least the optimal expected revenue:
--
--   $$R_i(S^*_i) \ge Z^*.$$
--
--   The proposition says that a nest worth offering anything in must earn at least the overall optimum; it is used, together with Lemma 3, to show that low-revenue products are never needed in an optimal assortment.
--
--   **Formalization Note** The standing assumptions of §3 (p. 13), $\gamma_i \le 1$ and $v_{i0} = 0$ for every nest, are hypotheses, together with those of §1 and the disclosed pins of the model definition ($v_{ij} > 0$, $r_{ij} \ge 0$, $\gamma_i > 0$, revenues ordered within each nest). The positivity $v_0 > 0$ is the section's own "without loss of generality" assumption (p. 14), stated as a hypothesis here because the argument uses it.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 14, Proposition 2

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

namespace NestedLogitVariants.Competitive

/-- Proposition 2, p. 14: if `(S*_1, …, S*_m)` is an optimal solution to problem (2) and
`S*_i ≠ ∅`, then `R_i(S*_i) ≥ Z*`. -/
theorem proposition_2 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal I Sstar)
    (i : ι) (hne : (Sstar i).Nonempty) :
    revenue I Sstar ≤ R I i (Sstar i) := by sorry

end NestedLogitVariants.Competitive
