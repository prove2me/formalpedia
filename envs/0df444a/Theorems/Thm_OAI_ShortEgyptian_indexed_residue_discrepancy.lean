-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_indexed_residue_discrepancy
-- name    : OAI.ShortEgyptian.indexed_residue_discrepancy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:35:17.726425+00:00
-- url     : https://prove2.me/theorems/6cb0886b-9e7c-4af0-bca8-647260e97380
-- title:
--   Fourier test for a family of residues: at least $\delta N/2$ of the $-v_i$ lie in $[0,\delta q)$
-- statement:
--   Let $q\ge1$ be an integer. For $x\in\mathbb{Z}/q\mathbb{Z}$ let $\bar x\in\{0,\dots,q-1\}$ be its least nonnegative representative and $e_q(x)=\exp(2\pi i\,\bar x/q)$. Let $(v_i)_{i\in\mathcal I}$ be a family of residues modulo $q$ indexed by a nonempty finite set $\mathcal I$ with $N=|\mathcal I|$ elements, and define its normalized character averages
--   $$\Phi(k)=\frac1N\sum_{i\in\mathcal I}e_q(k\,v_i),\qquad k\in\mathbb{Z}/q\mathbb{Z}.$$
--
--   Let $0<\delta\le1/256$, and let $H\ge1$ be an integer with $2H\delta^4\ge1$. Suppose that $|\Phi(l\bmod q)|\le\delta^3$ for every integer $l$ with $1\le l\le H$. Then
--
--   $$
--   \#\bigl\{\,i\in\mathcal I:\ \overline{-v_i}<\delta q\,\bigr\}\;\ge\;\frac{\delta N}{2}.
--   $$
--
--   In words: if the family $(v_i)$ shows no bias at the frequencies $1,\dots,H$, then at least a proportion $\delta/2$ of the indices have $-v_i$ in the initial window $[0,\delta q)$. Only positive frequencies have to be checked, because $\Phi(-k)=\overline{\Phi(k)}$. If $H\ge q$, the tested frequencies include $l=q$, where $\Phi(0)=1>\delta^3$; so the hypothesis can only hold when $H<q$.
--
--   **Formalization Note** The index set is a nonempty `Fintype α`, $N$ is `Fintype.card α`, and $\Phi$ is `indexedCharAverage v k = (∑ i, ZMod.stdAddChar (k * v i)) / card α`. The hypothesis quantifies over natural numbers `l` with `1 ≤ l ≤ H`, cast to `ZMod q`; $\overline{-v_i}$ is `(-v i).val`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/EmpiricalDiscrepancy.lean#L63-L98

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

theorem OAI.ShortEgyptian.indexed_residue_discrepancy {α : Type uα} [Fintype α] [Nonempty α]
    {q : ℕ} [NeZero q] (v : α → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256) (H : ℕ) (hH : 1 ≤ H)
    (hHδ : 1 ≤ 2 * (H : ℝ) * δ ^ 4)
    (hFourier : ∀ l : ℕ, 1 ≤ l → l ≤ H →
      ‖indexedCharAverage v (l : ZMod q)‖ ≤ δ ^ 3) :
    δ * Fintype.card α / 2 ≤ ((Finset.univ.filter fun i => ((-v i).val : ℝ) < δ * q).card : ℝ) := by sorry
