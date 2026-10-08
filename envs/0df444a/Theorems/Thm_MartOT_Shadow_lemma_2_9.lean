-- Prove2me | Theorems.Thm_MartOT_Shadow_lemma_2_9
-- name    : MartOT.Shadow.lemma_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:23.965255+00:00
-- url     : https://prove2.me/theorems/86340ac2-6f69-4600-9a54-f5ede1da62fd
-- title:
--   Lemma 2.9, p. 15 — every γ ∈ 𝓜 is the limit in 𝓜 of a ⪯C-increasing sequence of finitely supported measures below it
-- statement:
--   Let $\gamma$ be a finite Borel measure on $\mathbb R$ with finite first moment. Then there exists a sequence $(\gamma^{(n)})_{n\in\mathbb N}$ of finitely supported measures such that
--
--   1. $\gamma^{(n)}\preceq_C\gamma^{(n+1)}$ for every $n$ (increasing in the convex order);
--   2. $\gamma^{(n)}\to\gamma$ weakly in $\mathcal M$ (weak convergence together with convergence of $\int|x|$);
--   3. $\gamma^{(n)}\preceq_C\gamma$ for every $n$.
--
--   This approximation reduces statements about shadows of general measures to the case of finitely many atoms.
--
--   **Formalization Note** "Finitely supported" is "concentrated on a finite set": $\gamma^{(n)}(\mathbb R\setminus S_n)=0$ for a finite $S_n\subseteq\mathbb R$. The convex order $\preceq_C$ already contains membership in $\mathcal M$ of both sides.
-- source:
--   arXiv:1208.1509v2, Lemma 2.9, p. 15

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Definitions.Def_MartOT_Shadow_ConvergesInM

namespace MartOT.Shadow

open MeasureTheory

theorem lemma_2_9 (γ : Measure ℝ) (hγ : MartOT.Var.InM γ) :
    ∃ γs : ℕ → Measure ℝ, (∀ n, ∃ S : Finset ℝ, γs n (↑S : Set ℝ)ᶜ = 0) ∧
      (∀ n, MartOT.Var.ConvexLE (γs n) (γs (n + 1))) ∧ ConvergesInM γs γ ∧
      ∀ n, MartOT.Var.ConvexLE (γs n) γ := by sorry

end MartOT.Shadow
