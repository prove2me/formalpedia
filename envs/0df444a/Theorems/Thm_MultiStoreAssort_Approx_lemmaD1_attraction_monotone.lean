-- Prove2me | Theorems.Thm_MultiStoreAssort_Approx_lemmaD1_attraction_monotone
-- name    : MultiStoreAssort.Approx.lemmaD1_attraction_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:36.117811+00:00
-- url     : https://prove2.me/theorems/f712120c-f66d-4b82-907b-5d41201ccb3a
-- title:
--   Lemma D.1, PDF pp. 46–47 — shrinking MNL attraction values does not raise the optimal revenue
-- statement:
--   Consider an MNL model with $n$ products, revenues $r_1,\dots,r_n\in\mathbb R$ and attraction values $v_1,\dots,v_n>0$; the outside option has attraction value $1$. Let
--   $$
--   R=\max_{S}\frac{\sum_{i\in S}r_iv_i}{1+\sum_{i\in S}v_i},
--   $$
--   the maximum taken over all assortments $S\subseteq\{1,\dots,n\}$. Given $\epsilon_1,\dots,\epsilon_n$ with $0<\epsilon_i<1$, let
--   $$
--   R'=\max_{S}\frac{\sum_{i\in S}r_i\epsilon_iv_i}{1+\sum_{i\in S}\epsilon_iv_i}.
--   $$
--   Then $R\ge R'$.
--
--   The lemma says that the optimal MNL revenue is monotone in the attraction values. In the proof of Proposition 7 it bounds the revenue a store earns from the products of other stores, whose attraction values are discounted by $\exp(-c^k_i(\boldsymbol S))$, by the single-store optimum.
--
--   **Formalization Note.** The two optimal values are not formed as terms; the statement is: for every assortment $T$ there is an assortment $S$ whose revenue under $v$ is at least the revenue of $T$ under $\epsilon v$. No order or sign is assumed on the revenues, as in the lemma.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF pp. 46–47 (Online Supplement pp. 14–15), Lemma D.1

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_Approx_Model

namespace MultiStoreAssort.Approx

/-- Lemma D.1 (Online Supplement pp. 14–15): scaling every attraction value down by a factor
`ε_i ∈ (0, 1)` does not increase the optimal MNL revenue: `R ≥ R'`, where
`R = max_S MultiStoreAssort.SMR.single r v S` and `R' = max_S MultiStoreAssort.SMR.single r (ε v) S`. -/
theorem lemmaD1_attraction_monotone {n : ℕ} (r v ε : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (hε : ∀ i, 0 < ε i ∧ ε i < 1) :
    ∀ T : Finset (Fin n), ∃ S : Finset (Fin n), MultiStoreAssort.SMR.single r (fun i => ε i * v i) T ≤ MultiStoreAssort.SMR.single r v S := by sorry

end MultiStoreAssort.Approx
