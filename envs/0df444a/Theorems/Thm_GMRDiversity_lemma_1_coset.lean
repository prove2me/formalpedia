-- Prove2me | Theorems.Thm_GMRDiversity_lemma_1_coset
-- name    : GMRDiversity.lemma_1_coset
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:38:21.399+00:00
-- url     : https://prove2.me/theorems/825aea61-2e70-4f67-a213-bf8943bc2422
-- title:
--   Proof of Lemma 1 — $x\in\operatorname{span}(S,A)$ iff $A\in x+S$, so the probability is $|S|/2^n$
-- statement:
--   Let $S\le\mathbb F_2^n$ be a subspace and $x\notin S$. Then:
--
--   1. for every $a\in\mathbb F_2^n$, $x\in\operatorname{span}(S,a)$ if and only if $a\in x+S$;
--   2. for $a$ uniform on $\mathbb F_2^n$,
--   $$
--   \mathbb P\big(x\in\operatorname{span}(S,a)\big)=\frac{|S|}{2^n},\qquad |S|=2^{\dim S};
--   $$
--   3. if $\dim S\le\min\{w,j-1\}$, this probability is at most $2^{\min\{w,j-1\}-n}$.
--
--   In the proof of the lower bound, $S=S_j$ is the span of the pool before the $j$-th generation and $a=A_j$ the generated vector, which is uniform and independent of the history; this is the bound $\mathbb P(B_j\mid\mathcal H_{j-1})\le 2^{\min\{w,j-1\}-n}$.
--
--   Differences from the source:
--   - encoding: P(B_j | H_{j−1}) = 1_{E_j ∩ {x ∉ S_j}} |S_j|/2^n → for fixed S and x ∉ S, the uniform probability over a of x ∈ S ⊔ span{a}; a ∈ x + S written a − x ∈ S; reason: conditioning on H_{j−1} fixes S_j and x while A_j stays uniform; on {x ∈ S_j} or off E_j the indicator is 0
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), proof of Lemma 1, p.10

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Basic

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- **Proof of Lemma 1: the coset step** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with
Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, proof of Lemma 1,
p.10): let `S ≤ 𝔽₂ⁿ` and `x ∉ S`. Then
1. `x ∈ span(S, a)` if and only if `a ∈ x + S`;
2. for `a` uniform on `𝔽₂ⁿ`, `P(x ∈ span(S, a)) = |S| / 2ⁿ = 2^{dim S} / 2ⁿ`;
3. if `dim S ≤ min{w, j − 1}`, this probability is at most `2^{min{w, j−1} − n}`. -/
theorem lemma_1_coset {n : ℕ} (S : Submodule (ZMod 2) (V n)) (x : V n) (hx : x ∉ S) :
    (∀ a : V n, x ∈ S ⊔ Submodule.span (ZMod 2) {a} ↔ a - x ∈ S) ∧
    (PMF.uniformOfFintype (V n)).toOuterMeasure {a | x ∈ S ⊔ Submodule.span (ZMod 2) {a}}
      = (Nat.card S : ENNReal) / 2 ^ n ∧
    Nat.card S = 2 ^ Module.finrank (ZMod 2) S ∧
    (∀ w j : ℕ, Module.finrank (ZMod 2) S ≤ min w (j - 1) →
      (PMF.uniformOfFintype (V n)).toOuterMeasure {a | x ∈ S ⊔ Submodule.span (ZMod 2) {a}}
        ≤ (2 : ENNReal) ^ min w (j - 1) / 2 ^ n) := by sorry

end GMRDiversity
