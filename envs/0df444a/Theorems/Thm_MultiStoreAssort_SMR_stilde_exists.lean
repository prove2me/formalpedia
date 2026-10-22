-- Prove2me | Theorems.Thm_MultiStoreAssort_SMR_stilde_exists
-- name    : MultiStoreAssort.SMR.stilde_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:07.350849+00:00
-- url     : https://prove2.me/theorems/5713c183-db04-401d-a645-a2d3ae3d2b3b
-- title:
--   PDF p. 11 — some revenue-ordered assortment is optimal for the single-store problem (3), so S̃ exists
-- statement:
--   Let $r_1>r_2>\dots>r_n>0$ be product revenues and $v_1,\dots,v_n>0$ attraction values, with $n\ge 1$. Consider the single-store MNL assortment problem
--   $$R^*=\max_{S\subseteq\{1,\dots,n\}}\frac{\sum_{k\in S}r_kv_k}{1+\sum_{k\in S}v_k}.\tag{3}$$
--   Then some revenue-ordered assortment $\{1,\dots,k\}$ with $k\in[n]$ is optimal for (3). Consequently there is a smallest revenue-ordered optimal assortment, which the paper denotes $\tilde S$: an assortment $\tilde S$ that is revenue-ordered, optimal for (3), and has at most as many elements as every revenue-ordered optimal assortment.
--
--   The paper cites this fact from Talluri and van Ryzin (2004). It guarantees that $\tilde S$, the object every main result is phrased in terms of, exists.
--
--   **Formalization Note.** Products are indexed from $0$. The positivity $r_k>0$ is the series' standing assumption that revenues are prices. $n\ge 1$ is needed because a revenue-ordered set is nonempty by definition.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 11, §3, sentence after (3) (citing Talluri and van Ryzin 2004)

import Mathlib
import Definitions.Def_MultiStoreAssort_SMR_Model

namespace MultiStoreAssort.SMR

/-- p. 11 (Talluri–van Ryzin): some revenue-ordered assortment is optimal for (3), hence the
smallest revenue-ordered optimal assortment `S̃` exists. -/
theorem stilde_exists {n : ℕ} (r v : Fin n → ℝ) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k)
    (hv : ∀ k, 0 < v k) (hn : 0 < n) :
    ∃ St : Finset (Fin n), IsStilde r v St := by sorry

end MultiStoreAssort.SMR
