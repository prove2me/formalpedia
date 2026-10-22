-- Prove2me | Theorems.Thm_GelfandVNA_Duality_lemma_2_58
-- name    : GelfandVNA.Duality.lemma_2_58
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:23.045993+00:00
-- url     : https://prove2.me/theorems/15696341-512f-433f-809e-f6a6db38e7d0
-- title:
--   Lemma 2.58, p. 18 — normal valuations on a Stonean locale L ↔ continuous valuations on COpen(L)
-- statement:
--   Let $L$ be a Stonean locale and let $\mathrm{COpen}(L)$ be its complete Boolean algebra of compact opens, ordered as a subset of $L$ (so its suprema are $\sup R=\neg\neg\bigvee R$, computed in $L$ and then double-negated). Then restriction along the inclusion $\mathrm{COpen}(L)\to L$ is a bijection
--   $$\{\text{normal valuations } \nu\colon L\to\mathbb C\}\ \xrightarrow{\ \sim\ }\ \{\text{continuous valuations } \mu\colon\mathrm{COpen}(L)\to\mathbb C\},$$
--   and the same holds for real valuations with values in $\mathbb R$ and positive valuations with values in $[0,\infty)$. Precisely:
--
--   1. the restriction of a normal valuation $\nu$ on $L$ is a continuous valuation on $\mathrm{COpen}(L)$;
--   2. every continuous valuation $\mu$ on $\mathrm{COpen}(L)$ is the restriction of exactly one normal valuation on $L$;
--   3. and 4. the same two statements for real normal valuations and real continuous valuations;
--   5. and 6. the same two statements for positive normal valuations and positive continuous valuations.
--
--   The inverse is $\mu\mapsto\mu\circ\neg\neg$; this formula is forced by normality, $\nu(\neg\neg a)=\nu(a)$.
--
--   This is the bridge used for the hyperstonean duality (Proposition 2.73) and the Hahn–Jordan decomposition of normal valuations.
--
--   **Formalization Note** $\mathrm{COpen}(L)$ enters as an arbitrary lattice $B$ with bottom together with an order isomorphism $e$ from $B$ onto the poset of compact elements of $L$, so its lattice operations and suprema are its own, not those of $L$. Valuations are those of `QAlgorithms_Papers_Independent_Support21_P20` (Definitions 2.19, 2.57).
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 18, Lemma 2.58

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace GelfandVNA.Duality

open QAlgorithms.Papers.Independent.Support21.P20
open scoped NNReal

universe u

/-- Lemma 2.58, p. 18: for a Stonean locale `L`, restriction along `COpen(L) → L` is a bijection from
normal valuations on `L` onto continuous valuations on the complete Boolean algebra `COpen(L)`,
with inverse `μ ↦ μ ∘ ¬¬` (forced by normality, `ν(¬¬a) = ν(a)`). `COpen(L)` is any lattice `B` order-isomorphic (through `e`) to the
poset of compact opens of `L`; the statement is given for real, complex, and positive valuations. -/
theorem lemma_2_58 (L : Type u) [Order.Frame L] (hL : IsStoneanLocale L)
    (B : Type u) [Lattice B] [OrderBot B] (e : B ≃o {a : L // IsCompactElement a}) :
    (∀ ν : L → ℂ, IsNormalValuation ν → IsContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → ℂ, IsContinuousValuation μ →
      ∃! ν : L → ℂ, IsNormalValuation ν ∧ ∀ b, ν (e b) = μ b) ∧
    (∀ ν : L → ℝ, IsNormalValuation ν → IsContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → ℝ, IsContinuousValuation μ →
      ∃! ν : L → ℝ, IsNormalValuation ν ∧ ∀ b, ν (e b) = μ b) ∧
    (∀ ν : L → ℝ≥0, IsPositiveNormalValuation ν →
      IsPositiveContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → ℝ≥0, IsPositiveContinuousValuation μ →
      ∃! ν : L → ℝ≥0, IsPositiveNormalValuation ν ∧ ∀ b, ν (e b) = μ b) := by sorry

end GelfandVNA.Duality
