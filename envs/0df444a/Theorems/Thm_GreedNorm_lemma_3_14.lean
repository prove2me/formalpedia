-- Prove2me | Theorems.Thm_GreedNorm_lemma_3_14
-- name    : GreedNorm.lemma_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:01.750226+00:00
-- url     : https://prove2.me/theorems/a15a05ab-793f-4f58-9ba8-98cbb948b69a
-- title:
--   Lemma 3.14 — an exact polynomial-time algorithm for NormBudgCard
-- statement:
--   **Norm-Budgeted Cardinality Maximization** (NormBudgCard): given values $v(e)\ge0$ for the $n$ elements of $U$, a monotone symmetric norm $f$ on $\mathbb R^n$ and a budget $B\ge0$, find $S\subseteq U$ of maximum cardinality subject to $f(v[S])\le B$.
--
--   There are an admissible program $P$ of the deterministic value-oracle real RAM and constants $C,k\in\mathbb N$ such that for every $n$, every $v\in\mathbb R^n_{\ge0}$, every monotone symmetric norm $f$ and every $B\ge0$, the run of $P$ on input $(n, v, B)$ with oracle $f$ halts within $C(n+2)^k$ steps and outputs a set $S$ with
--
--   $$
--   f(v[S])\le B\quad\text{and}\quad |S'|\le |S|\ \text{ for every } S' \text{ with } f(v[S'])\le B .
--   $$
--
--   This is the subroutine (the BudgCard problem of GLB) that the framework of Section 3 needs, solved exactly ($\alpha=1$).
--
--   **Formalization Note** The machine is `GreedNorm.Machine` with $m=1$ and inner oracle $f$; the outer oracle is irrelevant and universally quantified. Input: integer cell $0$ holds $n$, cell $1$ holds $1$; real memory holds $v_j$ at address $j<n$ and $B$ at address $n$. Output: integer cell $2+j$ is $1$ if $j\in S$, else $0$.
--
--   Differences from the source:
--   - reading: there is an exact algorithm for NormBudgCard → one admissible program of the deterministic value-oracle real RAM that, on every instance, halts within C(n+2)^k steps with an optimal set; reason: the lemma is used inside the polynomial-time algorithm of Theorem 1.3; without a time bound the statement is trivial by enumeration; the degree is not printed, so it is existential
--   - encoding: monotone symmetric norms on the orthant R^k_{≥0} → R_{≥0} → functions (Fin k → ℝ) → ℝ satisfying the public SymNormLoad.IsMonotoneSymmetricNorm (a norm on all of ℝ^k, monotone on the orthant); reason: every monotone symmetric norm on the orthant extends to ℝ^k by x ↦ g(|x|), and only orthant values are ever used; same instances
--   - encoding: universe U of n elements, values v, budget B, output set S → U = Fin n; input in integer cells 0, 1 and real addresses 0..n; S encoded by integer cells 2 + j ∈ {0, 1}; reason: the paper fixes no encoding; any standard one is equivalent up to polynomial time
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Lemma 3.14 and Definition 3.13, p.9 (PDF 11)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_GreedNorm_vecOn
import Definitions.Def_GreedNorm_Machine

namespace GreedNorm

/-- **Lemma 3.14: an exact polynomial-time algorithm for NormBudgCard.**
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Lemma 3.14, p.9 (PDF 11): "There is an exact algorithm for NormBudgCard", for
Definition 3.13, p.9: "Given a universe U of n elements with value v(e) ≥ 0 for each element
e ∈ U, a monotone symmetric norm f : R^n → R≥0, a budget B ≥ 0, [...] find a subset S ⊆ U
maximizing |S| subject to the constraint that f(v[S]) ≤ B".

There is one admissible program `P` of the value-oracle real RAM `GreedNorm.Machine` and
constants `C, k` such that, for every `n`, every `v ≥ 0` in `ℝ^n`, every monotone symmetric norm
`f` and every `B ≥ 0`, the run of `P` with the single inner oracle `f` (`m = 1`) halts within
`C (n+2)^k` steps, and its output encodes a set `S` with `f(v[S]) ≤ B` of maximum cardinality.

**Formalization Note** Input: integer cell `0` holds `n`, cell `1` holds `1`; real memory holds
`v j` at address `j < n` and `B` at address `n`, `0` elsewhere. Output: on halting, integer cell
`2 + j` is `1` if `j ∈ S` and `0` otherwise. The outer oracle `g` is irrelevant and
universally quantified. "Exact algorithm" is read as exact and polynomial time (the lemma is used
inside the polynomial-time algorithm of Theorem 1.3); the degree `k` is existential. -/
theorem lemma_3_14 :
    ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C k : ℕ,
      ∀ (n : ℕ) (v : Fin n → ℝ), (∀ j, 0 ≤ v j) →
      ∀ (f : (Fin n → ℝ) → ℝ), SymNormLoad.IsMonotoneSymmetricNorm f →
      ∀ (B : ℝ), 0 ≤ B → ∀ (g : (Fin 1 → ℝ) → ℝ),
        let s₀ : Machine.State := Machine.init
          (fun a => (∑ j : Fin n, if a = (j : ℤ) then v j else 0) + if a = (n : ℤ) then B else 0)
          (fun a => if a = 0 then (n : ℤ) else if a = 1 then 1 else 0)
        ∃ t : ℕ, t ≤ C * (n + 2) ^ k ∧
          (Machine.run P (fun _ : Fin 1 => f) g s₀ t).halted = true ∧
          ∃ S : Finset (Fin n),
            (∀ j : Fin n, (Machine.run P (fun _ : Fin 1 => f) g s₀ t).integerMemory (2 + (j : ℤ)) =
              if j ∈ S then 1 else 0) ∧
            f (vecOn v S) ≤ B ∧
            ∀ S' : Finset (Fin n), f (vecOn v S') ≤ B → S'.card ≤ S.card := by sorry

end GreedNorm
