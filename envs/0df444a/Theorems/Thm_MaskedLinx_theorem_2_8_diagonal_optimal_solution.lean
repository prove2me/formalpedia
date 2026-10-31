-- Prove2me | Theorems.Thm_MaskedLinx_theorem_2_8_diagonal_optimal_solution
-- name    : MaskedLinx.theorem_2_8_diagonal_optimal_solution
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:06.070103+00:00
-- url     : https://prove2.me/theorems/b6d4ae0d-4f9f-4a64-9f8b-b73a369c7de4
-- title:
--   Theorem 2.8 — an optimal solution of the linx relaxation (1) for diagonal $C$
-- statement:
--   Let $C=\mathrm{Diag}(d)$ with $d\in\mathbb R^n$, $d_1\ge d_2\ge\dots\ge d_n>0$, and let $s$ be a natural number. Split the indices into
--
--   $$L=\{i: d_i<1\},\qquad E=\{i: d_i=1\},\qquad G=\{i: d_i>1\}.$$
--
--   Then the vector $\hat x$ below is an optimal solution of the linx relaxation (1):
--
--   1. If $s\le|G|$: let $\tilde x\in\mathbb R^{G}$ be an optimal solution of the problem (1) for $\tilde C=\mathrm{Diag}(d_i)_{i\in G}$ and $\tilde s=s$. Put $\hat x_i=\tilde x_i$ for $i\in G$ and $\hat x_i=0$ for $i\in E\cup L$.
--   2. If $|G|<s\le|G\cup E|$: let $\tilde x_i\in[0,1]$, $i\in E$, be any values with $\sum_{i\in E}\tilde x_i=s-|G|$. Put $\hat x_i=1$ for $i\in G$, $\hat x_i=\tilde x_i$ for $i\in E$ and $\hat x_i=0$ for $i\in L$.
--   3. If $|G\cup E|<s$: let $\tilde x\in\mathbb R^{L}$ be an optimal solution of the problem (1) for $\tilde C=\mathrm{Diag}(d_i)_{i\in L}$ and $\tilde s=s-|G\cup E|$. Put $\hat x_i=1$ for $i\in G\cup E$ and $\hat x_i=\tilde x_i$ for $i\in L$.
--
--   The theorem reduces the linx relaxation for a diagonal matrix to the two cases where all entries exceed $1$ or all are below $1$. In the paper it identifies the masked linx bound $\mathrm{linx}(C,s;I)=\mathrm{linx}(\mathrm{Diag}(\mathrm{diag}\,C),s)$ and underlies the optimal scaling of diagonal matrices.
--
--   **Formalization Note** Indices are `Fin n` (0-based), $d_1\ge\dots\ge d_n$ is `Antitone d`, and "optimal solution of (1)" is `IsOptimalSolution _ _ 1 _`. The subproblems are posed on the subtypes `{i // 1 < d i}` and `{i // d i < 1}` with the restricted diagonal; since $d$ is sorted these are the first $|G|$ and the last $|L|$ indices, i.e. the paper's $\tilde d_i=d_i$ and $\tilde d_i=d_{i+|G\cup E|}$. $|G\cup E|$ is the number of $i$ with $d_i\ge1$, and $s-|G\cup E|$ is natural-number subtraction, exact in case 3.
--
--   Differences from the source:
--   - generalization: x̃ is "the optimal solution" of the subproblem (1̃) → every optimal solution x̃ of (1̃); reason: the paper's "the" presumes uniqueness (Remark 2.4); the Lean statement needs no uniqueness and specializes to the unique solution
--   - encoding: subproblems on ℝ^{|G|}, ℝ^{|L|} with d̃ᵢ = dᵢ, d̃ᵢ = d_{i+|G∪E|} → subproblems on the subtypes {i // 1 < d i}, {i // d i < 1} of Fin n; reason: for sorted d the subtypes are the paper's index blocks in the same order, so the problems are the same
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, Theorem 2.8, p.5

import Mathlib
import Definitions.Def_MaskedLinx_IsOptimalSolution

namespace MaskedLinx

/-- **Theorem 2.8 (an optimal solution of (1) for diagonal `C`).**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, Theorem 2.8, p.5:
"Let C := Diag(d), where d ∈ ℝⁿ satisfies d₁ ≥ d₂ ≥ ··· ≥ dₙ > 0. Let L := {i ∈ N : dᵢ < 1},
E := {i ∈ N : dᵢ = 1}, and G := {i ∈ N : dᵢ > 1}. Then x̂ defined below is an optimal solution
for (1).
(i) If s ≤ |G|, let x̃ ∈ ℝ^{|G|} be the optimal solution of (1̃), which is (1) with (C,s) replaced
by (C̃,s̃) as follows: C̃ := Diag(d̃), where d̃ ∈ ℝ^{|G|}, d̃ᵢ := dᵢ, 1 ≤ i ≤ |G|, and s̃ := s. Then,
x̂ᵢ := x̃ᵢ, for i ∈ G; 0, for i ∈ E ∪ L.
(ii) If |G| < s ≤ |G ∪ E|, let x̃ᵢ, i ∈ E be any value such that 0 ≤ x̃ᵢ ≤ 1 and
Σ_{i∈E} x̃ᵢ = s − |G|. Then, x̂ᵢ := 1, for i ∈ G; x̃ᵢ, for i ∈ E; 0, for i ∈ L.
(iii) If |G ∪ E| < s, let x̃ ∈ ℝ^{|L|} be the optimal solution of (1̃), which is (1) with (C,s)
replaced by (C̃,s̃) as follows: C̃ := Diag(d̃) such that d̃ ∈ ℝ^{|L|}, d̃ᵢ = d_{i+|G∪E|},
1 ≤ i ≤ |L|, and s̃ := s − |G ∪ E|. Then, x̂ᵢ := 1, for i ∈ G ∪ E; x̃ᵢ, for i ∈ L."

**Formalization Note.** Indices are `Fin n` (0-based), `d₁ ≥ ⋯ ≥ dₙ` is `Antitone d`.
"Optimal solution of (1)" is `IsOptimalSolution _ _ 1 _` (γ = 1). The subproblems (1̃) are posed
on the subtypes `{i // 1 < d i}` (= G) and `{i // d i < 1}` (= L) with the restricted diagonal;
because `d` is sorted these are the first `|G|` and the last `|L|` indices, so this is the paper's
reindexing `d̃ᵢ = dᵢ`, `d̃ᵢ = d_{i+|G∪E|}`. `|G ∪ E|` is the number of `i` with `1 ≤ d i`.
In (i) and (iii) the conclusion is stated for **every** optimal solution `x̃` of (1̃) (the paper's
"the" presumes uniqueness, Remark 2.4). In (iii), `s − |G ∪ E|` is natural-number subtraction,
exact because `|G ∪ E| < s`. -/
theorem theorem_2_8_diagonal_optimal_solution (n : ℕ) (d : Fin n → ℝ) (hd : Antitone d)
    (hpos : ∀ i, 0 < d i) (s : ℕ) :
    -- (i)
    (s ≤ (Finset.univ.filter fun i => 1 < d i).card →
      ∀ xt : {i : Fin n // 1 < d i} → ℝ,
        IsOptimalSolution (Matrix.diagonal fun i : {i : Fin n // 1 < d i} => d i) s 1 xt →
        IsOptimalSolution (Matrix.diagonal d) s 1
          (fun i => if h : 1 < d i then xt ⟨i, h⟩ else 0)) ∧
    -- (ii)
    ((Finset.univ.filter fun i => 1 < d i).card < s →
      s ≤ (Finset.univ.filter fun i => 1 ≤ d i).card →
      ∀ xt : {i : Fin n // d i = 1} → ℝ, (∀ i, 0 ≤ xt i ∧ xt i ≤ 1) →
        ∑ i, xt i = (s : ℝ) - ((Finset.univ.filter fun i => 1 < d i).card : ℝ) →
        IsOptimalSolution (Matrix.diagonal d) s 1
          (fun i => if 1 < d i then 1 else if h : d i = 1 then xt ⟨i, h⟩ else 0)) ∧
    -- (iii)
    ((Finset.univ.filter fun i => 1 ≤ d i).card < s →
      ∀ xt : {i : Fin n // d i < 1} → ℝ,
        IsOptimalSolution (Matrix.diagonal fun i : {i : Fin n // d i < 1} => d i)
          (s - (Finset.univ.filter fun i => 1 ≤ d i).card) 1 xt →
        IsOptimalSolution (Matrix.diagonal d) s 1
          (fun i => if h : d i < 1 then xt ⟨i, h⟩ else 1)) := by sorry

end MaskedLinx
