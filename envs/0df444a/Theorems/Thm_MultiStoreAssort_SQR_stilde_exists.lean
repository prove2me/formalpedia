-- Prove2me | Theorems.Thm_MultiStoreAssort_SQR_stilde_exists
-- name    : MultiStoreAssort.SQR.stilde_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:52.591043+00:00
-- url     : https://prove2.me/theorems/ae521bc1-2732-43f8-961a-290977bef3f3
-- title:
--   PDF p. 11 — a smallest revenue-ordered optimal assortment S̃ of the single-store problem (3) exists
-- statement:
--   Let $r_1>r_2>\dots>r_n>0$ be product revenues and $v_1,\dots,v_n>0$ attraction values, with $n\ge 1$. Consider the single-store MNL assortment problem
--   $$
--   R^*=\max_{S\subseteq\{1,\dots,n\}}\ \frac{\sum_{k\in S} r_kv_k}{1+\sum_{k\in S}v_k}.
--   $$
--   At least one revenue-ordered assortment $\{1,\dots,k\}$, $k\in[n]$, is optimal (Talluri and van Ryzin 2004). Consequently there is a smallest revenue-ordered optimal assortment $\tilde S$: it is revenue-ordered, optimal, and has no more elements than any other revenue-ordered optimal assortment.
--
--   This sentence makes the paper's $\tilde S$ well defined; every result of the mission that mentions $\tilde S$ assumes it, so this statement shows that hypothesis can be met.
--
--   **Formalization Note.** Revenues are assumed positive (they are prices); $n\ge 1$ is needed because revenue-ordered sets are nonempty.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 11, §3, sentence after (3) (citing Talluri and van Ryzin 2004)

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

namespace MultiStoreAssort.SQR

theorem stilde_exists {n : ℕ} (r v : Fin n → ℝ) (hn : 0 < n) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) :
    ∃ St : Finset (Fin n), MultiStoreAssort.SMR.IsStilde r v St := by sorry

end MultiStoreAssort.SQR
