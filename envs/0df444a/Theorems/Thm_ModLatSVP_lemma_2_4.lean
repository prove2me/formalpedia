-- Prove2me | Theorems.Thm_ModLatSVP_lemma_2_4
-- name    : ModLatSVP.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:58.0192+00:00
-- url     : https://prove2.me/theorems/3e518b2d-b2ff-430a-bf18-26104c967f5f
-- title:
--   Lemma 2.4 — the final search or a dyadic rescaling $a=2^{-q}$ satisfying (10) reaches the search conditions
-- statement:
--   Let $M$ be a module of rank $r\ge2$ over a totally real or CM field, with a module flag whose projected suffix is reduced, block minima $H_i$, first-block minimum $H=H_1$, and prefix bounds $R_j$. For $0<a\le1$ write $R_j(a)=a^{1/j}R_j$ and $G_a$ for the Gram matrix with lengths in the first block scaled by $a$.
--
--   1. If $R_j>H/2$ for every $j\ge2$, the flag satisfies the search conditions at radius $R=H$, and $M\cap B(0,H)$ contains a shortest nonzero vector of $M$.
--   2. Otherwise there is a dyadic factor $a=2^{-q}\in(0,1]$ such that
--   $$\min_{j\ge2}R_j(a)\le aH/2,\qquad R_j(a)>aH/4\ \text{ for every }j\ge2. \tag{10}$$
--   With the first block scaled by $a$, every prefix $M_{j_0}$ attaining the minimum in (10) satisfies the search conditions at radius $R=aH/2$; it contains a nonzero vector of scaled length at most $aH/2$, and every nonzero vector of $M_{j_0}$ of scaled length at most $aH/2$ has length at most $H/2$ in the original metric.
--
--   This is the step of Algorithm 1 that either finishes with a complete search at radius $H$ or halves $H$ while keeping every search under the control of Lemma 2.3.
--
--   Differences from the source:
--   - encoding: a module flag 0 = V_0 ⊂ ⋯ ⊂ V_r = M ⊗ ℚ of a rank-r module M → the module ℤ^{r×d} written in an adapted basis, V_i spanned by the first i blocks, action matrices block upper triangular (IsModuleFlag); reason: every flag has an adapted basis (§2.2, App. B.2) and every quantity involved is invariant under the change of basis
--   - encoding: G_i = det(L_i)^{1/d} → (g_i / g_{i−1})^{1/(2d)}, g_i the principal minor of the Gram matrix on the first i blocks; reason: det(L_i)² = g_i / g_{i−1} by the Schur-complement formula (43)
--   - generalization: a module in the input model, with positive definite rational Gram matrix G → any positive definite real Gram matrix G; reason: specializes to rational G by casting; the proof does not use rationality
--   - reading: one can compute a dyadic factor a = 2^{−q} ∈ (0, 1] such that (10) → there is q : ℕ such that a = (1/2)^q satisfies (10); reason: the computation (finite search with exact rational comparisons, (45)) belongs to the algorithm, whose cost Theorems 3.4, 3.5 and the goal carry
--   - reading: Searching this prefix finds a nonzero vector whose length in the original metric is at most H/2 → the prefix contains a nonzero vector of scaled length ≤ aH/2, and every nonzero vector of the prefix of scaled length ≤ aH/2 has original length ≤ H/2; reason: the search returns some vector of scaled length ≤ R = aH/2; the bound must hold for whichever one it returns
--   - encoding: the Gram matrix G_a of (44) → a²G + (1 − a²)P with P the Gram matrix of π_{V_1^⊥} (scaledGram); reason: expanding the blocks gives (44) exactly
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Lemma 2.4, §2.4, (10), p.16 (PDF p.16); proof App. B.3, (44)–(45), pp.49–50

import Mathlib
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_SearchCond

open NumberField

namespace ModLatSVP

/-- **Lemma 2.4, §2.4, p.16 (full proof App. B.3, pp.49–50).** Kim, Lee, Son, *Exact SVP and CVP in
Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript
sha256 e7151fad…): "Let a flag of rank r ≥ 2 have a reduced projected suffix, and let H = H₁. If
R_j > H/2 for every j ≥ 2, the flag satisfies the search conditions at radius R = H, and M ∩ B(0, H)
contains a shortest vector of M. Otherwise, one can compute a dyadic factor a = 2^{−q} ∈ (0, 1] such that
min_{j≥2} R_j(a) ≤ aH/2, R_j(a) > aH/4 for every j ≥ 2. (10) With the first block scaled by a, a prefix
attaining the minimum in (10) satisfies the search conditions at radius R = aH/2. Searching this prefix
finds a nonzero vector whose length in the original metric is at most H/2."

Here `R_j(a) = a^{1/j} R_j` (p.16) and the scaled metric is the Gram matrix `G_a` of (44)
(`scaledGram`).
1. If `R_j > H/2` for all `2 ≤ j ≤ r`: the search conditions hold at `R = H`, and some shortest nonzero
   vector of `M` has length at most `H`.
2. Otherwise there is `q ∈ ℕ` such that `a = 2^{−q}` satisfies (10), and for every `2 ≤ j₀ ≤ r` attaining
   `min_{j ≥ 2} R_j(a)`: the prefix `M_{j₀}` with metric `G_a` satisfies the search conditions at
   `R = aH/2`, it contains a nonzero vector of scaled length at most `aH/2`, and every nonzero vector of
   `M_{j₀}` of scaled length at most `aH/2` has original length at most `H/2`.

**Formalization Note.** "One can compute a dyadic factor" is read as the existence of `q`; the
computation (a finite search with exact rational comparisons, (45)) is part of the algorithm, whose
cost Theorems 3.4, 3.5 and the goal carry. "Searching this prefix finds a nonzero vector …" is stated
as: such vectors exist, and every vector the search can return satisfies the bound. -/
theorem lemma_2_4 (K : Type*) [Field K] [NumberField K] (hK : IsTotallyReal K ∨ IsCMField K)
    (τ : K ≃ₐ[ℚ] K) (hτ : IsStar K τ) (r d : ℕ) (hr : 2 ≤ r)
    (G : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (φ : K →+* Matrix (Fin r × Fin d) (Fin r × Fin d) ℚ)
    (hM : IsModuleFlag K τ r d G φ) (hsuf : ∀ i : ℕ, 2 ≤ i → i ≤ r → ReducedAt G r i) :
    ((∀ j : ℕ, 2 ≤ j → j ≤ r → blockMin G 1 / 2 < prefixBound G j) →
        SearchCond G r (blockMin G 1) ∧
          ∃ x : Fin r × Fin d → ℤ, x ≠ 0 ∧ Real.sqrt (qf G (intVec x)) ≤ blockMin G 1 ∧
            ∀ y : Fin r × Fin d → ℤ, y ≠ 0 → qf G (intVec x) ≤ qf G (intVec y)) ∧
      ((∃ j : ℕ, 2 ≤ j ∧ j ≤ r ∧ prefixBound G j ≤ blockMin G 1 / 2) →
        ∃ q : ℕ,
          (∃ j : ℕ, 2 ≤ j ∧ j ≤ r ∧
            ((1 / 2 : ℝ) ^ q) ^ ((1 : ℝ) / j) * prefixBound G j ≤ (1 / 2 : ℝ) ^ q * blockMin G 1 / 2) ∧
          (∀ j : ℕ, 2 ≤ j → j ≤ r →
            (1 / 2 : ℝ) ^ q * blockMin G 1 / 4 < ((1 / 2 : ℝ) ^ q) ^ ((1 : ℝ) / j) * prefixBound G j) ∧
          ∀ j₀ : ℕ, 2 ≤ j₀ → j₀ ≤ r →
            (∀ j : ℕ, 2 ≤ j → j ≤ r →
              ((1 / 2 : ℝ) ^ q) ^ ((1 : ℝ) / j₀) * prefixBound G j₀ ≤
                ((1 / 2 : ℝ) ^ q) ^ ((1 : ℝ) / j) * prefixBound G j) →
            SearchCond (scaledGram G ((1 / 2 : ℝ) ^ q)) j₀ ((1 / 2 : ℝ) ^ q * blockMin G 1 / 2) ∧
            (∃ x : Fin r × Fin d → ℤ, InPrefixZ j₀ x ∧ x ≠ 0 ∧
              Real.sqrt (qf (scaledGram G ((1 / 2 : ℝ) ^ q)) (intVec x)) ≤
                (1 / 2 : ℝ) ^ q * blockMin G 1 / 2) ∧
            ∀ x : Fin r × Fin d → ℤ, InPrefixZ j₀ x → x ≠ 0 →
              Real.sqrt (qf (scaledGram G ((1 / 2 : ℝ) ^ q)) (intVec x)) ≤
                (1 / 2 : ℝ) ^ q * blockMin G 1 / 2 →
              Real.sqrt (qf G (intVec x)) ≤ blockMin G 1 / 2) := by sorry

end ModLatSVP
