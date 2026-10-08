-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_lemma1
-- name    : NesterovRCD.Sublinear.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:13.034724+00:00
-- url     : https://prove2.me/theorems/406a6d70-44fa-4c29-b775-c001b3e39f79
-- title:
--   Lemma 1 — $A_{i,i}\preceq L_iB_i$ for all blocks implies $A\preceq(\sum_iL_i)\,\mathrm{diag}\{B_i\}$
-- statement:
--   Fix a decomposition of $\mathbb R^m$ into $k$ coordinate subspaces, given by assigning each coordinate $j$ to a block $\mathrm{blk}(j)\in\{1,\dots,k\}$, and write $x^{(i)}$ for the vector that agrees with $x$ on the coordinates of block $i$ and is $0$ elsewhere. Let $A\in\mathbb R^{m\times m}$ be symmetric positive semidefinite, and let $B_1,\dots,B_k$ be matrices that are positive semidefinite on their blocks, $\langle B_ix^{(i)},x^{(i)}\rangle\ge0$. Let $L_1,\dots,L_k\ge0$. If the diagonal blocks of $A$ satisfy $A_{i,i}\preceq L_iB_i$, that is,
--   $$\langle Ax^{(i)},x^{(i)}\rangle\le L_i\langle B_ix^{(i)},x^{(i)}\rangle\qquad\text{for all }x\text{ and }i,$$
--   then $A\preceq\big(\sum_{i=1}^kL_i\big)\cdot\mathrm{diag}\{B_i\}_{i=1}^k$, that is, for every $x\in\mathbb R^m$
--   $$\langle Ax,x\rangle\le\Big(\sum_{i=1}^kL_i\Big)\sum_{i=1}^k\langle B_ix^{(i)},x^{(i)}\rangle .$$
--
--   The lemma compares a positive semidefinite matrix with the block-diagonal matrix built from bounds on its diagonal blocks; it is the matrix form of the fact that block-wise curvature bounds give a global bound at the price of the factor $\sum_iL_i$.
--
--   **Formalization Note** The paper writes $\mathbb R^n$ for the ambient space, which is `Fin m → ℝ` here. Only the $(i,i)$ block of $B_i$ enters, through $x^{(i)}$. The paper's "(n × N)-matrix" is a typo for a square matrix. The hypothesis $L_i\ge0$ is implicit in the paper (its proof takes $L_i^{1/2}$) and is stated explicitly. Blocks are allowed to be empty.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 4, Lemma 1 (first claim)

import Mathlib

namespace NesterovRCD.Sublinear

open Matrix

theorem lemma1 {m k : ℕ} (blk : Fin m → Fin k) (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (B : Fin k → Matrix (Fin m) (Fin m) ℝ) (L : Fin k → ℝ) (hL : ∀ i, 0 ≤ L i)
    (hB : ∀ (i : Fin k) (x : Fin m → ℝ),
      0 ≤ (fun j => if blk j = i then x j else 0) ⬝ᵥ
        (B i *ᵥ fun j => if blk j = i then x j else 0))
    (hAB : ∀ (i : Fin k) (x : Fin m → ℝ),
      (fun j => if blk j = i then x j else 0) ⬝ᵥ (A *ᵥ fun j => if blk j = i then x j else 0)
        ≤ L i * ((fun j => if blk j = i then x j else 0) ⬝ᵥ
          (B i *ᵥ fun j => if blk j = i then x j else 0)))
    (x : Fin m → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ (∑ i, L i) *
      ∑ i, (fun j => if blk j = i then x j else 0) ⬝ᵥ
        (B i *ᵥ fun j => if blk j = i then x j else 0) := by sorry

end NesterovRCD.Sublinear
