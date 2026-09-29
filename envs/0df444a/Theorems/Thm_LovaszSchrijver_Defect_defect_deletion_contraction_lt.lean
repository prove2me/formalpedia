-- Prove2me | Theorems.Thm_LovaszSchrijver_Defect_defect_deletion_contraction_lt
-- name    : LovaszSchrijver.Defect.defect_deletion_contraction_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:54:52.303323+00:00
-- url     : https://prove2.me/theorems/8815d5b5-edb8-41fb-8b5d-d46e2606be5b
-- title:
--   Proof of Theorem 2.13 — deletion and contraction of the half-integral node have smaller defect
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes, and let $a^{\mathsf T}x \le b$ be an inequality with $a \in \mathbb Z_+^V$, $b \in \mathbb Z_+$, valid for $\mathrm{STAB}(G)$, whose defect
--   $$r = 2\max\{a^{\mathsf T}x - b : x \in \mathrm{FRAC}(G)\}$$
--   is positive. Let $i \in V$ be a node with $y_i = \tfrac12$ at every vector $y \in \mathrm{FRAC}(G)$ maximizing $a^{\mathsf T}x$ (such a node exists by Lemma 2.12). Then both the deletion and the contraction of $i$ result in constraints with smaller defect:
--
--   1. the deletion $a_{V-i}^{\mathsf T}x \le b$ has a defect, and it is $< r$;
--   2. the contraction $a_{V-\Gamma(i)-i}^{\mathsf T}x \le b - a_i$ has a defect, and it is $< r$.
--
--   This is the claim on which the induction on $r$ in the upper bound of Theorem 2.13 rests.
--
--   **Formalization Note** Deletion and contraction are the zero-extended coefficient vectors on the same graph $G$ (see the definition item), and their defects are taken over $\mathrm{FRAC}(G)$, as in the paper's proof. The contraction's right-hand side $b - a_i$ is computed in $\mathbb R$. The existence of each defect (the maximum being attained) is part of the conclusion.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 182, proof of Theorem 2.13 (upper bound), second paragraph

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_Index

namespace LovaszSchrijver.Defect

theorem defect_deletion_contraction_lt {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℕ) (b : ℕ) (hvalid : Valid (STAB G) (fun j => (a j : ℝ)) b)
    (r : ℝ) (hr : IsDefect G (fun j => (a j : ℝ)) b r) (hr0 : 0 < r)
    (i : V) (hi : ∀ y : V → ℝ, IsFRACMaximizer G (fun j => (a j : ℝ)) y → y i = 1 / 2) :
    (∃ r₁ : ℝ, IsDefect G (deletion (fun j => (a j : ℝ)) i) b r₁ ∧ r₁ < r) ∧
    (∃ r₂ : ℝ, IsDefect G (contraction G (fun j => (a j : ℝ)) i) ((b : ℝ) - (a i : ℝ)) r₂ ∧
      r₂ < r) := by sorry

end LovaszSchrijver.Defect
