-- Prove2me | Theorems.Thm_LiftSAParity_lemma_3_4_pseudo_measure
-- name    : LiftSAParity.lemma_3_4_pseudo_measure
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:04.73328+00:00
-- url     : https://prove2.me/theorems/de339ca4-88bb-4230-8786-e801f604caef
-- title:
--   Lemma 3.4 — pseudo-measures on affine spaces bound semantic SA(⊕) coefficient size
-- statement:
--   Let $\varphi$ be an unsatisfiable CNF formula over $N$ variables, $r$ a positive integer and $\delta>0$. Let $\mu$ assign a value $\mu(A)\ge0$ to every nonempty affine space $A\subseteq\mathbb F_2^N$ of codimension at most $r$, such that
--
--   1. $\mu(\{0,1\}^N)=1$;
--   2. $|\mu(A)-\mu(A\cap\{f=0\})-\mu(A\cap\{f=1\})|\le\delta$ for every linear form $f$ and every $A$ with $\operatorname{codim}A\le r-1$ on which $f$ is non-constant;
--   3. $\mu(A_C\cap A)\le\delta$ for every clause $C$ of $\varphi$ and every $A$ with $A_C\cap A$ nonempty and $\operatorname{codim}(A_C\cap A)\le r$;
--   4. $\mu(A)\le\delta$ for every $A$ with $\operatorname{codim}A=r$.
--
--   Then every semantic SA(⊕) refutation of $\varphi$ has coefficient size at least
--   $$\frac1\delta .$$
--
--   This is the specialization of the pseudo-measure duality (Proposition 3.3) to semantic SA(⊕) that the lifting theorem uses: it reduces the size lower bound to the construction of one function on low-codimension affine spaces.
--
--   **Formalization Note** $\mu$ is a real function on all subsets of $\mathbb F_2^N$, constrained only on nonempty affine spaces of codimension at most $r$ (the paper's codimension is defined for nonempty spaces).
--
--   Differences from the source:
--   - encoding: a non-negative measure on affine linear spaces of codimension at most r → a real function on all subsets, nonnegative and constrained only on nonempty affine spaces of codimension ≤ r; reason: codimension is defined only for nonempty spaces (§2, p.7); the extra values are never read
--   - encoding: a CNF formula over N variables → a CNF formula over a finite type V; reason: V is [N] up to relabelling
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §3.2, p.12, Lemma 3.4

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_SemSAXorRefutation

namespace LiftSAParity

/-- **Lemma 3.4** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), p.12): the pseudo-measure criterion for semantic SA(⊕). Let φ be an
unsatisfiable CNF formula over the variables `V`, `r` a positive integer and `δ > 0`. Let `µ`
be nonnegative on the nonempty affine spaces of codimension at most `r`, with
(1) `µ(𝔽₂^V) = 1`;
(2) `|µ(A) − µ(A ∩ {f = 0}) − µ(A ∩ {f = 1})| ≤ δ` for every linear form `f` and every `A` with
`codim A ≤ r − 1` and `f` non-constant on `A`;
(3) `µ(A_C ∩ A) ≤ δ` for every clause `C` of φ and every `A` with `codim(A_C ∩ A) ≤ r`;
(4) `µ(A) ≤ δ` for every `A` with `codim A = r`.
Then every semantic SA(⊕) refutation of φ has coefficient size at least `1/δ`.

**Formalization Note** "Affine space" in (2)–(4) is a nonempty affine space (the paper's codimension
is defined for nonempty spaces only); `µ` is a function on all subsets, constrained only on those. -/
theorem lemma_3_4_pseudo_measure {V : Type*} [Fintype V] [DecidableEq V] (φ : CNF V)
    (hφ : ¬ Satisfiable φ) (r : ℕ) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ)
    (μ : Set (V → ZMod 2) → ℝ)
    (hnonneg : ∀ A, IsAffineSpace A → A.Nonempty → codim A ≤ r → 0 ≤ μ A)
    (h1 : μ Set.univ = 1)
    (h2 : ∀ (S : Finset V) (A : Set (V → ZMod 2)), IsAffineSpace A → A.Nonempty →
      codim A ≤ r - 1 → ¬ IsConstOn S A → |μ A - μ (slice A S 0) - μ (slice A S 1)| ≤ δ)
    (h3 : ∀ C ∈ φ, ∀ A : Set (V → ZMod 2), IsAffineSpace A → (falsifySpace C ∩ A).Nonempty →
      codim (falsifySpace C ∩ A) ≤ r → μ (falsifySpace C ∩ A) ≤ δ)
    (h4 : ∀ A, IsAffineSpace A → A.Nonempty → codim A = r → μ A ≤ δ)
    (π : SemSAXorRefutation φ) : 1 / δ ≤ π.coeffSize := by sorry

end LiftSAParity
