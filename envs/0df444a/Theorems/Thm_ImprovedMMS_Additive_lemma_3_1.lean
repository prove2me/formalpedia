-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_lemma_3_1
-- name    : ImprovedMMS.Additive.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:31.93382+00:00
-- url     : https://prove2.me/theorems/fae28e9c-7bce-4c32-8ecc-6df021d2f44c
-- title:
--   Lemma 3.1, p. 17 — in an α-irreducible instance no agent values a single good at α or more
-- statement:
--   Let the agents of an instance $(\mathcal N,\mathcal M)$ have additive non-negative valuations, normalised so that $\mathsf{MMS}_i=1$ for every $a_i\in\mathcal N$. If the instance is $\alpha$-irreducible, then
--   $$V_i(\{b_j\})<\alpha\qquad\text{for every } a_i\in\mathcal N \text{ and } b_j\in\mathcal M.$$
--
--   With $\alpha=3/4$: in a $3/4$-irreducible instance no single good satisfies an agent.
--
--   **Formalization Note** The normalisation $\mathsf{MMS}_i=1$ is the standing assumption of §3 (p. 14: "Throughout this section, we assume $\mathsf{MMS}_i=1$ for all agents"); it is a hypothesis here. Without it the conclusion would read $V_i(\{b_j\})<\alpha\,\mathsf{MMS}_i$.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 17, Lemma 3.1 (standing assumption MMS_i = 1, p. 14)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance
open LittleCharity.MMS

namespace ImprovedMMS.Additive

/-- Lemma 3.1 (p. 17), under the §3 normalization `MMS_i = 1` (p. 14): in an `α`-irreducible
instance every agent values every single good below `α`. -/
theorem lemma_3_1 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hv : IsAdditive v)
    (N : Finset (Fin n)) (M : Finset (Fin m)) (hN1 : ∀ i ∈ N, mms (v i) N.card M = 1)
    (α : ℝ) (hirr : IsIrreducible α v N M) :
    ∀ i ∈ N, ∀ b ∈ M, v i {b} < α := by sorry

end ImprovedMMS.Additive
