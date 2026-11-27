-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_6
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:38:47.25949+00:00
-- url     : https://prove2.me/theorems/d3e88895-b2eb-4aea-9992-b7d80d5522b0
-- title:
--   Theorem 6, p. 14 — deterministic outside option u_0 < u_i: Q_i(u^+) = (9) and Q_0(u^+) = G_0(u^+)
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. Add an **outside option** $0$ with deterministic utility $u_0$, and suppose $u_i>u_0$ for every $i\in N$. Let $Q_i(\mathbf u^+,\boldsymbol\lambda)=P\{u_i-z_i\ge u_0\text{ and }u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ for $i\in N$, $Q_0(\mathbf u^+,\boldsymbol\lambda)=P\{u_0\ge u_j-z_j\ \forall j\in N\}$, $G_0=\exp[-\sum_{j\in N}\lambda_j(u_j-u_0)]$ and $L=\sum_{k\in N}\lambda_k$. Then for every $i\in N$
--   $$
--   Q_i(\mathbf u^+,\boldsymbol\lambda)=G_i(\mathbf u^+,\boldsymbol\lambda)-\sum_{k\in W_i^-\setminus\{0\}}\frac{\lambda_i}{L_k^+}\,G_k(\mathbf u^+,\boldsymbol\lambda)-\frac{\lambda_i}{L}\,G_0(\mathbf u^+,\boldsymbol\lambda),\qquad(9)
--   $$
--   and $Q_0(\mathbf u^+,\boldsymbol\lambda)=G_0(\mathbf u^+,\boldsymbol\lambda)$.
--
--   The outside option takes demand from each choice in proportion to its error rate; this is the demand model of the monopoly analysis.
--
--   **Formalization Note** The paper defines $B_i$, $B_i^+$ and $W_i^-$ over $N^+=N\cup\{0\}$. Because $u_0<u_i$ for every $i$, the sets $B_i$ and $B_k^+$ over $N^+$ never contain $0$, so $G_i(\mathbf u^+)$ and $L_k^+(\mathbf u^+)$ are the published `G u lam i` and `Lplus u lam k` over $N$, and $W_i^-\setminus\{0\}$ is `strictlyWorse u i`. For $k\in W_i^-$, $L_k^+\ge\lambda_i>0$.
--
--   Differences from the source:
--   - encoding: G_i(u^+), L_k^+(u^+), W_i^−∖{0} over N^+ = N ∪ {0} → G u lam i, Lplus u lam k, strictlyWorse u i over N; reason: under the hypothesis u_0 < u_i the index 0 never belongs to B_i or B_k^+, so the values coincide
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 14, §3.4 and Theorem 6, (9); proof p. 50

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_6 {n : ℕ} (hn : 2 ≤ n) (u₀ : ℝ) (u lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hu₀ : ∀ i, u₀ < u i) :
    (∀ i, choiceProbOut u₀ u lam i =
        G u lam i - ∑ k ∈ strictlyWorse u i, lam i / Lplus u lam k * G u lam k -
          lam i / Ltot lam * G0 u₀ u lam) ∧
      outsideProb u₀ u lam = G0 u₀ u lam := by sorry

end HetExponomial.ChoiceProb.Supplement
