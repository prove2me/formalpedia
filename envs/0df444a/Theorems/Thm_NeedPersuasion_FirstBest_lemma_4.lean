-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_lemma_4
-- name    : NeedPersuasion.FirstBest.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:49.502982+00:00
-- url     : https://prove2.me/theorems/1cf65124-89d4-481f-b8c1-a3f184595631
-- title:
--   Lemma 4, p. 37 — equilibrium of the no-information mechanism: p_ni = 1, 0, or the root of Σ(λ_L p + λ_H)^k u_L(k) = 0
-- statement:
--   For $p\in[0,1]$ let $\pi(p)$ be given by $\pi_n(p)=(1-\lambda_Lp-\lambda_H)(\lambda_Lp+\lambda_H)^n$. Under the no-information mechanism ni every low-need user joins with the same probability $p^{ni}$, and the steady state is $\pi(p^{ni})\in\Pi_{SM}$, where $p^{ni}\in[0,1]$ satisfies:
--
--   1. if $\sum_{k=0}^\infty\lambda^ku_L(k)\ge0$ then $p^{ni}=1$;
--   2. if $\sum_{k=0}^\infty\lambda_H^ku_L(k)\le0$ then $p^{ni}=0$;
--   3. otherwise $p^{ni}\in(0,1)$ and
--   $$\sum_{k=0}^\infty(\lambda_Lp^{ni}+\lambda_H)^ku_L(k)=0 .$$
--
--   Precisely: an equilibrium $p$ exists; for every equilibrium $p$, $\pi(p)\in\Pi_{SM}$; and every equilibrium satisfies the condition of the case that applies.
--
--   **Formalization Note** In cases 1 and 2 the series is required to converge before its sign is read (at $\lambda=1$ the series of case 1 diverges to $-\infty$, which falls under "otherwise"); case 3 asserts that the series converges with sum $0$. Existence of an equilibrium is stated under finite high-need welfare, since an equilibrium requires $\pi(p)$ to be an admission policy, which includes finite welfare.
-- source:
--   arXiv:2005.07253v3, Lemma 4, p. 37

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

namespace NeedPersuasion.FirstBest

theorem lemma_4 (M : Model) (hM : M.Standing) :
    (FiniteHWelfare M → ∃ p, IsNIEquilibrium M p) ∧
    (∀ p, IsNIEquilibrium M p → niDist M p ∈ PiSM M) ∧
    ((Summable (fun k => M.lam ^ k * M.uL k) ∧ 0 ≤ ∑' k, M.lam ^ k * M.uL k) →
      ∀ p, IsNIEquilibrium M p → p = 1) ∧
    ((Summable (fun k => M.lamH ^ k * M.uL k) ∧ ∑' k, M.lamH ^ k * M.uL k ≤ 0) →
      ∀ p, IsNIEquilibrium M p → p = 0) ∧
    (¬ (Summable (fun k => M.lam ^ k * M.uL k) ∧ 0 ≤ ∑' k, M.lam ^ k * M.uL k) →
      ¬ (Summable (fun k => M.lamH ^ k * M.uL k) ∧ ∑' k, M.lamH ^ k * M.uL k ≤ 0) →
      ∀ p, IsNIEquilibrium M p →
        p ∈ Set.Ioo (0 : ℝ) 1 ∧ HasSum (fun k => (M.lamL * p + M.lamH) ^ k * M.uL k) 0) := by sorry

end NeedPersuasion.FirstBest
