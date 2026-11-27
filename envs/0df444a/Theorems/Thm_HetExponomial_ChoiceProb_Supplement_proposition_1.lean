-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_proposition_1
-- name    : HetExponomial.ChoiceProb.Supplement.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:36:30.582312+00:00
-- url     : https://prove2.me/theorems/dc09bb99-cdfc-4587-8ec6-05569fe885d1
-- title:
--   Proposition 1, p. 9 (corrected: (5) with W_j^− in place of W_i, the two agree when u_i < u_j) — recursions (5), (6) for adjacent choices
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. Let $i\ne j$ be **adjacent** choices with $u_i\le u_j$: no other choice $k$ has $u_i<u_k<u_j$. Write $W_i=\{k: u_k\le u_i\}$ and $W_j^-=\{k: u_k<u_j\}$. Then
--
--   1. (recursion (5), printed form) if $u_i<u_j$,
--   $$
--   Q_j(\mathbf u,\boldsymbol\lambda)=G_j(\mathbf u,\boldsymbol\lambda)-\frac{\lambda_j}{L_j}\sum_{k\in W_i}Q_k(\mathbf u,\boldsymbol\lambda);
--   $$
--   2. (recursion (5), corrected form, for $u_i\le u_j$)
--   $$
--   Q_j(\mathbf u,\boldsymbol\lambda)=G_j(\mathbf u,\boldsymbol\lambda)-\frac{\lambda_j}{L_j}\sum_{k\in W_j^-}Q_k(\mathbf u,\boldsymbol\lambda);
--   $$
--   3. (recursion (6), for $u_i\le u_j$)
--   $$
--   Q_j(\mathbf u,\boldsymbol\lambda)=G_j(\mathbf u,\boldsymbol\lambda)-\frac{\lambda_jL_i}{\lambda_iL_j}\,G_i(\mathbf u,\boldsymbol\lambda)+\frac{\lambda_j}{\lambda_i}\,Q_i(\mathbf u,\boldsymbol\lambda).
--   $$
--
--   These recursions compute the choice probabilities one adjacent choice at a time, from the lowest ideal utility upwards. The proof of Theorem 2 uses (5) in the form of item 2 (with $j=i$'s own worse set $W_i^-$).
--
--   **Formalization Note** When $u_i<u_j$ adjacency gives $W_i=W_j^-$, so items 1 and 2 coincide there.
--
--   Differences from the source:
--   - correction: (5) with the sum over W_i = {k : u_k ≤ u_i}, for all adjacent u_i ≤ u_j → (5) as printed when u_i < u_j, and (5) with the sum over W_j^− = {k : u_k < u_j} for all adjacent u_i ≤ u_j; reason: as printed, (5) fails when u_i = u_j: for n = 2, u_1 = u_2, W_i = N, so the right side is λ_j/L − λ_j/L = 0 while Q_j = λ_j/L; the proof on p. 46 uses W_i = W_j^−, which holds exactly when u_i < u_j, and the proof of Theorem 2 (p. 46) quotes (5) with W_i^−; see DISPROOF.md
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 9, Proposition 1, (5)–(6); proof on pp. 46–47; use of (5) in the proof of Theorem 2, p. 46

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem proposition_1 {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i j : Fin n) (hadj : Adjacent u i j) :
    (u i < u j →
        choiceProb u lam j =
          G u lam j - lam j / Lsum u lam j * ∑ k ∈ worse u i, choiceProb u lam k) ∧
      choiceProb u lam j =
        G u lam j - lam j / Lsum u lam j * ∑ k ∈ strictlyWorse u j, choiceProb u lam k ∧
      choiceProb u lam j =
        G u lam j - lam j * Lsum u lam i / (lam i * Lsum u lam j) * G u lam i +
          lam j / lam i * choiceProb u lam i := by sorry

end HetExponomial.ChoiceProb.Supplement
