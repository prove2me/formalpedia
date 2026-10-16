-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_convolution_discrepancy
-- name    : OAI.ShortEgyptian.convolution_discrepancy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:30:28.4916+00:00
-- url     : https://prove2.me/theorems/26687e5f-957f-446f-bfc9-2efb5fa221cf
-- title:
--   Fourier lower bound for the mass of a set containing a sumset in $\mathbb{Z}/q\mathbb{Z}$
-- statement:
--   Let $q\ge1$ be an integer and write $e_q(x)=e^{2\pi i x/q}$ for $x\in\mathbb{Z}/q\mathbb{Z}$, which is well defined because it depends only on $x$ modulo $q$. For a set $A\subseteq\mathbb{Z}/q\mathbb{Z}$ and a function $\mu:\mathbb{Z}/q\mathbb{Z}\to\mathbb{R}$ define, for $k\in\mathbb{Z}/q\mathbb{Z}$,
--   $$
--   \widehat{1_A}(k)=\sum_{a\in A}e_q(ka),\qquad\widehat\mu(k)=\sum_{x\in\mathbb{Z}/q\mathbb{Z}}\mu(x)\,e_q(-kx).
--   $$
--   Let $A,B,I\subseteq\mathbb{Z}/q\mathbb{Z}$, and let $\mu$ be a probability distribution on $\mathbb{Z}/q\mathbb{Z}$, i.e. $\mu(x)\ge0$ for all $x$ and $\sum_x\mu(x)=1$. Suppose that $a+b\in I$ for all $a\in A$ and $b\in B$. Then, with $\mu(I)=\sum_{x\in I}\mu(x)$,
--
--   $$
--   |A|\,|B|-\sum_{k\ne0}\bigl|\widehat{1_A}(k)\bigr|\,\bigl|\widehat{1_B}(k)\bigr|\,\bigl|\widehat\mu(k)\bigr|\le q\,|B|\,\mu(I),
--   $$
--
--   where the sum runs over the nonzero residues $k\in\mathbb{Z}/q\mathbb{Z}$.
--
--   When $B\ne\emptyset$ this can be read as $\mu(I)\ge\frac{|A|}{q}-\frac1{q|B|}\sum_{k\ne0}|\widehat{1_A}(k)|\,|\widehat{1_B}(k)|\,|\widehat\mu(k)|$. A set containing a sumset $A+B$ thus receives at least about its expected share $|A|/q$ of the mass, up to an error controlled by the nontrivial Fourier coefficients of $\mu$. This is a basic discrepancy inequality: distributions with small Fourier coefficients give substantial mass to windows of residues (with $A$, $B$ intervals) or to any fixed set (with $B=\{0\}$ and $A=I$).
--
--   **Formalization Note** $e_q$ is Mathlib's standard additive character `ZMod.stdAddChar`, $\widehat{1_A}$ is `charSum A`, and $\widehat\mu$ is `probabilityFourier μ`. The condition $q\ge1$ is the instance `[NeZero q]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/FourierDiscrepancy.lean#L90-L136

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.convolution_discrepancy {q : ℕ} [NeZero q] (A B I : Finset (ZMod q))
    (μ : ZMod q → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1)
    (hsupport : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ I) :
    (A.card : ℝ) * B.card -
        ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ‖charSum A k‖ * ‖charSum B k‖ * ‖probabilityFourier μ k‖ ≤
      (q : ℝ) * B.card * ∑ x ∈ I, μ x := by sorry
