-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_Supplement_theorem_4
-- name    : MusicStreaming.Axioms.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:26:58.529046+00:00
-- url     : https://prove2.me/theorems/c12e0127-0768-4f9a-b48d-9dba4cc4a496
-- title:
--   Theorem 4, p. 16 — pro-rata and user-centric as weighted proportional and two-stage claims rules (R^{P,P} and R^{CEA,P})
-- statement:
--   Let $(N,M,t)$ be a streaming problem with $m=|M|$ users, and let $(N,K,c,E)=(N,M,t,m)$ be the associated claims problem. Write $P$ for the pro-rata index, $U$ for the user-centric index, and $R^P,R^U$ for the rewards they induce, $R^I_i=\frac{I_i}{\sum_{i'}I_{i'}}\,m$. Then:
--
--   1. There exist weight functions $\omega^P$ and $\omega^U$ such that, for every streaming problem,
--   $$R^P(N,M,t)=P^{\omega^P}(N,K,c,E)\quad\text{and}\quad R^U(N,M,t)=P^{\omega^U}(N,K,c,E).$$
--   2. The pro-rata rewards are given by the two-stage rule that uses the proportional rule in both stages:
--   $$R^P(N,M,t)=R^{P,P}(N,K,c,E).$$
--   3. The user-centric index is the two-stage rule that uses constrained equal awards in the first stage and the proportional rule in the second:
--   $$U(N,M,t)=R^{CEA,P}(N,K,c,E).$$
--
--   All equalities are equalities of vectors over the artists. Here $P^\omega$ is the weighted proportional rule, $R^{\psi,\varphi}$ the two-stage rule of the bankruptcy rules $\psi,\varphi$, and $P$ and $CEA$ in the superscripts are the proportional and constrained equal awards bankruptcy rules. The theorem places the two indices inside the families of claims rules studied by Ju et al. (2007) and in the multi-issue allocation literature.
--
--   **Formalization Note** Artists are `Fin n`, users are natural numbers and a streaming problem is the published finitely supported stream table with natural-number entries, as in the base mission; its user set is the set of users with a nonzero column, so every user total $T^j$ is at least $1$. The weight functions in (a) are families over all finite issue sets $K\subseteq\mathbb N$ that read the issue totals only on $K$, with the probability-vector property for nonempty $K$. For the empty problem all sides are the zero vector.
--
--   Differences from the source:
--   - generalization: for the given streaming problem there exist weight functions $\omega^P,\omega^U$ → one pair $(\omega^P,\omega^U)$ serves every number of artists and every streaming problem; reason: the weight functions of p. 26 do not depend on the problem, and the uniform statement implies the per-problem one.
--   - reading: first-stage claims printed $c^K_j=\sum_{i\in N}c_{ji}$ and second-stage problem $(N,\psi_j(K,E,c^K),c_{\cdot j})$ → $c^K_j=\sum_{i\in N}c_{ij}$ and $\varphi_i(N,c_{\cdot j},\psi_j(K,c^K,E))$; reason: index order and argument order are fixed by the dimensions, the final display of p. 16 and the computations on pp. 26–27.
--   - encoding: $\lambda$ in $CEA$ "satisfies $\sum\min\{\lambda,c_i\}=E$" → one chosen solution $\lambda\ge0$, and $0$ when none exists; reason: on valid problems the awards do not depend on the chosen solution, and every first-stage problem here is valid.
--   - encoding: weight function $\omega:\mathbb R^K_+\times\mathbb R_+\to\mathbb R^K_+$ → a family indexed by finite $K\subseteq\mathbb N$, local in $(C^j)_{j\in K}$, a probability vector for nonempty $K$; reason: the empty issue set occurs only for the empty streaming problem, where every rule gives $0$.
--   - encoding: $N=\{1,\dots,n\}$, users $M=\{1,\dots,m\}$, $t$ a matrix → artists `Fin n`, users named by natural numbers, $t$ a finitely supported table of natural numbers whose support is $M$; reason: the base mission's published model; it covers every streaming problem.
--   - encoding: divisions $c_{ij}/C^j$ and $c_i/\sum c_{i'}$ → Lean division with $x/0=0$; reason: on streaming data every $C^j\ge1$, and a zero denominator occurs only with an empty sum.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 16, Theorem 4 (proof pp. 26–27)

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting
import Definitions.Def_MusicStreaming_Axioms_Supplement_Bankruptcy
import Definitions.Def_MusicStreaming_Axioms_Supplement_Claims
import Definitions.Def_MusicStreaming_Axioms_Supplement_TwoStage
import Definitions.Def_MusicStreaming_Axioms_Supplement_AssociatedClaims

namespace MusicStreaming.Axioms.Supplement

open MusicStreaming.Axioms

theorem theorem_4 :
    (∃ ωP ωU : WeightFunction ℕ, IsWeightFunction ωP ∧ IsWeightFunction ωU ∧
      ∀ (n : ℕ) (t : Problem n),
        reward proRata t = weightedProportional ωP (assocClaims t) ∧
        reward userCentric t = weightedProportional ωU (assocClaims t)) ∧
    (∀ (n : ℕ) (t : Problem n),
      reward proRata t = twoStage proportional proportional (assocClaims t)) ∧
    (∀ (n : ℕ) (t : Problem n),
      userCentric t = twoStage cea proportional (assocClaims t)) := by sorry

end MusicStreaming.Axioms.Supplement
