-- Prove2me | Theorems.Thm_GirthBethe_Sharp_sharp_girth_bethe_permanent
-- name    : GirthBethe.Sharp.sharp_girth_bethe_permanent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:21:01.272194+00:00
-- url     : https://prove2.me/theorems/c858fe72-802b-4908-904b-2ee45a6a7682
-- title:
--   Theorem 1.3 — $\mathrm{Bethe}(A)\le\mathrm{per}(A)\le2^{2n/g}\mathrm{Bethe}(A)$ for support girth $\ge g$, sharp when $g\mid2n$
-- statement:
--   Let $n\ge1$ and let $g\ge4$ be even.
--
--   1. For every matrix $A\in\mathbb R^{n\times n}$ with nonnegative entries whose support graph $G_A$ has girth at least $g$ (forests have infinite girth),
--   $$\mathrm{Bethe}(A)\le\mathrm{per}(A)\le2^{2n/g}\,\mathrm{Bethe}(A),$$
--   with the real exponent $2n/g$.
--   2. Whenever $g\mid2n$, the upper bound is attained by the 0–1 matrices whose support graphs are disjoint unions of cycles of length $g$: such matrices exist, and every such matrix $A$ satisfies
--   $$\mathrm{per}(A)=2^{2n/g}\,\mathrm{Bethe}(A).$$
--
--   The theorem confirms Anari's conjecture (Conjecture 1.1), refines the universal bound $\mathrm{per}(A)\le2^{n/2}\mathrm{Bethe}(A)$ of Anari and Rezaei (the case $g=4$), and is optimal for every even girth.
--
--   **Formalization Note** Entries are arbitrary nonnegative reals; there is no assumption of positive permanent, of a perfect matching, or of nonempty $\mathrm{PM}(G_A)$. The sharpness clause does not classify all equality cases.
--
--   Differences from the source:
--   - encoding: A ∈ ℝ^{n×n}_{≥0} with rows and columns indexed by [n] → A : Matrix (Fin n) (Fin n) ℝ with ∀ i j, 0 ≤ A i j (0-based indices); reason: relabelling only
--   - encoding: per(A) = ∑_σ ∏_i A_{i,σ(i)} → Matrix.permanent A = ∑_σ ∏_i A_{σ(i), i}; reason: the two sums agree under σ ↦ σ⁻¹
--   - encoding: Bethe(A) := max over PM(G_A) in (1.1) → bethe A := sSup of the Bethe objective over PM(G_A) (0 if PM(G_A) = ∅), real powers with x^0 = 1; reason: the maximum is attained (item bethe_max_attained), so the supremum is the maximum; real powers give the boundary values 1 at p_e = 0 and A_e at p_e = 1, which are the limits by continuity
--   - encoding: support graph of girth at least g → (g : ℕ∞) ≤ (supportGraph A).egirth; reason: egirth is the shortest cycle length and ⊤ for a forest
--   - encoding: support graph a disjoint union of cycles of length g → every vertex of G_A has exactly two neighbours and every connected component has exactly g vertices; reason: a finite connected 2-regular simple graph is a cycle whose length is its number of vertices
--   - encoding: the upper bound is attained by these matrices → such a 0–1 matrix exists, and per(A) = 2^{2n/g} Bethe(A) for every one of them; reason: explicit reading of 'attained by the matrices', including that the family is nonempty (Example 1.2)
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 3, Theorem 1.3 (with Example 1.2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_BethePermanent

open Finset

namespace GirthBethe.Sharp

/-- Theorem 1.3: for even `g ≥ 4` and nonnegative `A` with support girth at least `g`, `Bethe(A) ≤ per(A) ≤ 2^{2n/g} Bethe(A)`; when `g ∣ 2n` the upper bound is attained by the 0–1 matrices whose support graphs are disjoint unions of `g`-cycles (such matrices exist). -/
theorem sharp_girth_bethe_permanent (n : ℕ) (hn : 0 < n) (g : ℕ) (hg : Even g) (hg4 : 4 ≤ g) :
    (∀ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 ≤ A i j) →
        (g : ℕ∞) ≤ (supportGraph A).egirth →
        bethe A ≤ A.permanent ∧
          A.permanent ≤ (2 : ℝ) ^ ((2 * n : ℝ) / g) * bethe A) ∧
      (g ∣ 2 * n →
        (∃ A : Matrix (Fin n) (Fin n) ℝ, IsZeroOne A ∧
            IsDisjointUnionOfCycles (supportGraph A) g) ∧
          ∀ A : Matrix (Fin n) (Fin n) ℝ, IsZeroOne A →
            IsDisjointUnionOfCycles (supportGraph A) g →
            A.permanent = (2 : ℝ) ^ ((2 * n : ℝ) / g) * bethe A) := by sorry

end GirthBethe.Sharp
