-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_lemma_4_12
-- name    : InterleavedUnitaryNOF.LowerBound.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:00.031597+00:00
-- url     : https://prove2.me/theorems/647f84b0-a39a-4c4c-8721-e294b1c8f60b
-- title:
--   Lemma 4.12 — weighted product estimates, both clauses
-- statement:
--   There is a universal $\kappa_0>0$ for which both weighted estimates below hold. Put $\mathcal G=SU(m)$, $\mathcal H=SU(m)^2$ and $\lambda_0=31/30$. Unconditioned means use independent normalized Haar variables. Conditioning on a product equal to $T$ means sampling $A,B,C$ independently and setting $D=(ABC)^{-1}T$.
--
--   1. For every $T\in\mathcal G$ and measurable $a,b:\mathcal G^2\to[0,1]$,
--
--   $$\mathbb E[ab\mid ABCD=T]\le\lambda_0\mathbb E[a]\mathbb E[b]+e^{-\kappa_0\sqrt m}.$$
--
--   2. For every $L\in\mathcal H$ and measurable $a,b:\mathcal H^2\to[0,1]$, with coordinatewise multiplication,
--
--   $$\mathbb E[ab\mid ABCD=L]\le\lambda_0^2\mathbb E[a]\mathbb E[b]+(1+\lambda_0)e^{-\kappa_0\sqrt m}.$$
--
--   Both conclusions use the same constant, uniformly over dimensions, functions and specified products.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable [0,1]-valued functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and real functions bounded pointwise by Set.Icc 0 1; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - encoding: κ₀ supplied by Theorem 4.11 and conditioning on specified products → a single positive existential κ₀ uniform across both displayed sampling estimates; reason: no draft theorem is imported or assumed; the witnesses of these estimates and 4.11 can be made common by taking their positive minimum
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Lemma 4.12, printed p.14 = PDF p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem lemma_4_12 : ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ (m : ℕ) [NeZero m],
    (∀ (T : SU m) (a b : SU m × SU m → ℝ),
      Measurable a → Measurable b → (∀ x, a x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ x, b x ∈ Set.Icc (0 : ℝ) 1) →
      productAverage (haar m) T a b ≤
        ((31 : ℝ)/30) * pairAverage (haar m) a * pairAverage (haar m) b +
          Real.exp (-κ₀*Real.sqrt m)) ∧
    (∀ (L : Duo m) (a b : Duo m × Duo m → ℝ),
      Measurable a → Measurable b → (∀ x, a x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ x, b x ∈ Set.Icc (0 : ℝ) 1) →
      productAverage (haarPower m 2) L a b ≤
        ((31 : ℝ)/30)^2 * pairAverage (haarPower m 2) a * pairAverage (haarPower m 2) b +
          (1+(31 : ℝ)/30)*Real.exp (-κ₀*Real.sqrt m)) := by sorry

end InterleavedUnitaryNOF.LowerBound
