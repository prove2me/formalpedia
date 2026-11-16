-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_Supplement_lemma_5
-- name    : IQPForrelation832.SingleQuery.Supplement.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:57:01.152278+00:00
-- url     : https://prove2.me/theorems/a51c8311-ab8b-40fd-96c2-28d54ee4f6e8
-- title:
--   Lemma 5 — Fourier decomposition under every restriction
-- statement:
--   Let $c$ be any $d$-query IQP circuit on $m$ qubits with an $n$-wire phase oracle, and fix any restriction $\rho$, with free set $\Gamma$. Compute $v_A$ from the actual circuit and put $v_C^\rho=\sum_{A\cap\Gamma=C}\epsilon_A(\rho)v_A$. For every free sign assignment $x$, the actual pre-final-Hadamard state satisfies
--   $$
--   |\psi_{x\rho}\rangle=\sum_{C\subseteq\Gamma,\,|C|\le d}\chi_C(x)|v_C^\rho\rangle.
--   $$
--   These vectors are pairwise orthogonal, their squared norms sum to one, and $v_C^\rho=0$ when $|C|>d$:
--   $$
--   C\ne D\Rightarrow\langle v_C^\rho,v_D^\rho\rangle=0,\qquad
--   \sum_{C\subseteq\Gamma}\|v_C^\rho\|_2^2=1.
--   $$
--   The result covers overlapping and repeated query registers, arbitrary diagonal middle gates, all-fixed and all-free restrictions, and zero dimensions or queries. The vectors are defined by grouping computational-basis amplitudes, so none of these conclusions is assumed. This is the shared support for Theorems 5 and 6.
--
--   Differences from the source:
--   - generalization: polynomial-size IQP middle blocks → arbitrary finite diagonal-unitary middle gate lists; reason: the Section 5 arguments do not use the number of non-oracle gates; every source circuit is included
--   - encoding: sign assignments on the free set Gamma and its subsets → Boolean signs on the exact free-coordinate subtype; reason: true represents +1 and false represents -1; all assignments and restrictions correspond bijectively, including the empty free set
--   - generalization: a sum over C ⊆ Γ with |C| ≤ d → the same expansion plus the separate clause v_C^ρ = 0 whenever |C| > d; reason: an added conclusion, the last sentence of the source's proof (C = A ∩ Γ implies |C| ≤ |A| ≤ d); it implies the displayed expansion and removes nothing
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 25, Lemma 5; proof pp. 26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Supplement_OracleFourier

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery.Supplement

open QAlgorithms QAlgorithms.Complexity

theorem lemma_5 {n m d : ℕ} (c : PhaseMiddle n m)
    (hc : PhaseIQP c) (hd : OracleCircuit.queryCount c 0 = d) (ρ : Restriction n) :
    (∀ x : FreeAssignment ρ, phaseBefore c (extendRestriction ρ x) =
      ∑ C : Finset {a : Cube n // a ∈ freeSet ρ},
        if C.card ≤ d then (oracleCharacter ρ C x : ℂ) • restrictedVector c ρ C else 0) ∧
    (∀ C D : Finset {a : Cube n // a ∈ freeSet ρ}, C ≠ D →
      inner ℂ (restrictedVector c ρ C) (restrictedVector c ρ D) = 0) ∧
    (∑ C : Finset {a : Cube n // a ∈ freeSet ρ}, ‖restrictedVector c ρ C‖^2) = 1 ∧
    (∀ C : Finset {a : Cube n // a ∈ freeSet ρ}, d < C.card →
      restrictedVector c ρ C = 0) := by sorry

end IQPForrelation832.SingleQuery.Supplement
