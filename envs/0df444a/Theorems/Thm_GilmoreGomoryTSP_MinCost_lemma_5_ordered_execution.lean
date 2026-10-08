-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_lemma_5_ordered_execution
-- name    : GilmoreGomoryTSP.MinCost.lemma_5_ordered_execution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:44:40.048728+00:00
-- url     : https://prove2.me/theorems/4f086f68-3dd1-4172-b105-28805dce57fb
-- title:
--   Lemma 5 — executed in the right order, adjacent interchanges on φ have additive cost
-- statement:
--   Let $B$ be sorted, $f,g$ locally integrable with $f+g\ge0$, and $\varphi$ the minimal cost permutation that ranks the $A$. Let $\alpha_{i_1,i_1+1},\dots,\alpha_{i_m,i_m+1}$ be distinct adjacent interchanges, $i_1<\dots<i_m$. Execute them on $\varphi$ in the following order: first all type-1 interchanges (lower node $q$ with $B_q\le A_{\varphi(q)}$) in decreasing order of index, then all type-2 interchanges in increasing order of index. The resulting permutation $\psi'$ satisfies
--   $$c(\psi') = c(\varphi)+\sum_{p=1}^{m} c_\varphi(\alpha_{i_p,i_p+1}).$$
--
--   The order matters: in general later interchanges change the cost of earlier ones. This lemma supplies the cost half of Theorem 3.
--
--   **Formalization Note** The paper states "obtained by executing the $\alpha$'s in a particular order" and specifies the order in the proof (p. 664); the Lean statement uses that explicit order (`execOrder`), which is stronger than an existential over orders. The set of interchanges is an arbitrary finite set $T$ of lower indices.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 664, Lemma 5 and the execution order stated in its proof

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem lemma_5_ordered_execution {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (T : Finset (Fin n)) :
    cost f g A B (applyAdj φ (execOrder A B φ T)) =
      cost f g A B φ + adjTreeCost f g A B φ T := by sorry

end GilmoreGomoryTSP.MinCost
