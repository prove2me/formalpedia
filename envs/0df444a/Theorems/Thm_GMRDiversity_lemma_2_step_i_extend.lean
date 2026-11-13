-- Prove2me | Theorems.Thm_GMRDiversity_lemma_2_step_i_extend
-- name    : GMRDiversity.lemma_2_step_i_extend
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:39:41.7592+00:00
-- url     : https://prove2.me/theorems/d84b0a86-8476-4faf-b21e-c8f7e904203b
-- title:
--   Proof of Lemma 2, Step (i) — adjoining one or two vectors keeps $S$ nondegenerate
-- statement:
--   Let $S\le\mathbb F_2^n$ be nondegenerate and $H:=S^\perp$.
--
--   1. If $a=s+h$ with $s\in S$, $h\in H$ and $h\cdot h=1$, then $\operatorname{span}(S,a)$ is nondegenerate and has dimension $\dim S+1$.
--   2. If $h\cdot h=0$ for every $h\in H$, and $a_i=s_i+h_i$ with $s_i\in S$, $h_i\in H$ $(i=1,2)$ and $h_1\cdot h_2=1$, so that the Gram matrix of $h_1,h_2$ is $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$, then $\operatorname{span}(S,a_1,a_2)$ is nondegenerate and has dimension $\dim S+2$.
--   3. If $h\cdot h\ne0$ for some $h\in H$, then exactly half of the elements of $H$ satisfy $h\cdot h=1$.
--   4. For every nonzero $h_1\in H$, exactly half of the elements of $H$ satisfy $h_1\cdot h=1$.
--
--   With the uniformity of $h_a$ (Step (i), decomposition), items 3 and 4 say that each "generate until" in Step (i) succeeds with probability $1/2$ per generation, so it takes two generations in expectation.
--
--   Differences from the source:
--   - encoding: 'generate until h_a · h_a = 1, which takes two generations in expectation'; 'both take constant expected generations' → exactly half of H satisfies the condition (items 3–4); reason: with h_a uniform on H, each generation succeeds with probability 1/2, a geometric number of trials with mean 2
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 2, Step (i), pp.10–11

import Mathlib
import Definitions.Def_GMRDiversity_Nondeg

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 2, Step (i): the one- and two-vector extensions** (Brandenberger, Doron-Arad,
Mossel, *Genetic Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript
sha256 f89f4f77…, proof of Lemma 2, Step (i), pp.10–11): let `S ≤ 𝔽₂ⁿ` be nondegenerate,
`H := S^⊥`.
1. If `a = s + h` with `s ∈ S`, `h ∈ H`, `h · h = 1`, then `span(S, a)` is nondegenerate of dimension
   `dim S + 1`.
2. If `h · h = 0` for every `h ∈ H`, and `aᵢ = sᵢ + hᵢ` with `sᵢ ∈ S`, `hᵢ ∈ H`, `h₁ · h₂ = 1` (Gram
   matrix `(0 1; 1 0)`), then `span(S, a₁, a₂)` is nondegenerate of dimension `dim S + 2`.
3. If `h ↦ h · h` is not identically zero on `H`, exactly half of `H` has `h · h = 1`.
4. For every nonzero `h₁ ∈ H`, exactly half of `H` has `h₁ · h = 1`.
Items 3 and 4, with the uniformity of `h_a`, are why "generate until …" takes a constant expected
number of generations. -/
theorem lemma_2_step_i_extend {n : ℕ} (S : Submodule (ZMod 2) (V n)) (hS : Nondeg S) :
    (∀ s h a : V n, s ∈ S → h ∈ orth S → dot h h = 1 → a = s + h →
      Nondeg (S ⊔ Submodule.span (ZMod 2) {a}) ∧
      Module.finrank (ZMod 2) ↥(S ⊔ Submodule.span (ZMod 2) {a}) =
        Module.finrank (ZMod 2) S + 1) ∧
    ((∀ h ∈ orth S, dot h h = 0) →
      ∀ s₁ s₂ h₁ h₂ a₁ a₂ : V n, s₁ ∈ S → s₂ ∈ S → h₁ ∈ orth S → h₂ ∈ orth S →
        dot h₁ h₂ = 1 → a₁ = s₁ + h₁ → a₂ = s₂ + h₂ →
        Nondeg (S ⊔ Submodule.span (ZMod 2) {a₁, a₂}) ∧
        Module.finrank (ZMod 2) ↥(S ⊔ Submodule.span (ZMod 2) {a₁, a₂}) =
          Module.finrank (ZMod 2) S + 2) ∧
    ((∃ h ∈ orth S, dot h h ≠ 0) →
      2 * Nat.card {h : V n // h ∈ orth S ∧ dot h h = 1} = Nat.card (orth S)) ∧
    (∀ h₁ ∈ orth S, h₁ ≠ 0 →
      2 * Nat.card {h : V n // h ∈ orth S ∧ dot h₁ h = 1} = Nat.card (orth S)) := by sorry

end GMRDiversity
