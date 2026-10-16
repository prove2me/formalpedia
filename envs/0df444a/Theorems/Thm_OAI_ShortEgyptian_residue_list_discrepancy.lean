-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_residue_list_discrepancy
-- name    : OAI.ShortEgyptian.residue_list_discrepancy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:38:12.344758+00:00
-- url     : https://prove2.me/theorems/081d5685-e284-4f01-b437-6deb8f6b4d8b
-- title:
--   Fourier criterion for many small greedy remainders $q\lceil Qt_i/q\rceil-Qt_i<\delta q$
-- statement:
--   Write $e(x)=\exp(2\pi i x)$. Let $(t_i)_{i\in\mathcal I}$ be a family of positive integers indexed by a nonempty finite set $\mathcal I$ with $N=|\mathcal I|$ elements, and let $Q\ge1$ and $q\ge1$ be integers. For each $i$ put
--   $$r_i=q\left\lceil\frac{Q\,t_i}{q}\right\rceil-Q\,t_i ,$$
--   the distance from $Qt_i$ up to the least multiple of $q$ that is at least $Qt_i$; thus $0\le r_i<q$ and $r_i\equiv-Qt_i\pmod q$. Let $0<\delta\le1/256$, and suppose that for every integer $l$ with $1\le l\le\lfloor\delta^{-4}\rfloor$,
--   $$\Bigl|\frac1N\sum_{i\in\mathcal I}e\!\left(\frac{l\,Q\,t_i}{q}\right)\Bigr|\le\delta^3 .$$
--   Then
--
--   $$
--   \#\{\,i\in\mathcal I:\ r_i<\delta q\,\}\;\ge\;\frac{\delta N}{2}.
--   $$
--
--   The remainder $r_i$ has a direct Egyptian-fraction meaning: with $z_i=\lceil Qt_i/q\rceil$ one has $\frac{q}{Qt_i}-\frac1{z_i}=\frac{r_i}{Qt_i\,z_i}$, so $r_i$ is the numerator left after one greedy step applied to $q/(Qt_i)$. The theorem guarantees that, under a Fourier non-bias condition on the numbers $Qt_i$ modulo $q$, a proportion at least $\delta/2$ of the indices leave a numerator smaller than $\delta q$.
--
--   **Formalization Note** The ceiling is `quotient v u = ⌈(v : ℚ) / u⌉₊` and $r_i$ is `residue (Q * t i) q (quotient (Q * t i) q)`, where `residue v u z = u * z - v` uses truncated natural subtraction (harmless here, since $q\lceil v/q\rceil\ge v$). The exponential is `phase`, and the bound $\lfloor\delta^{-4}\rfloor$ is `⌊1 / δ ^ 4⌋₊` (`Nat.floor`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ResidueDiscrepancy.lean#L48-L74

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy

open OAI OAI.ShortEgyptian
universe uα
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.residue_list_discrepancy {α : Type uα} [Fintype α] [Nonempty α]
    (t : α → ℕ) (Q q : ℕ) (hQ : 0 < Q) (hq : 0 < q) (ht : ∀ i, 0 < t i)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256)
    (hFourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖(∑ i, phase ((l : ℝ) * Q * t i / q)) / (Fintype.card α : ℂ)‖ ≤ δ ^ 3) :
    δ * Fintype.card α / 2 ≤
      ((Finset.univ.filter fun i => (residue (Q * t i) q (quotient (Q * t i) q) : ℝ) < δ * q).card : ℝ) := by sorry
