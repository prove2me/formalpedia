-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_window_spectral_tail
-- name    : OAI.ShortEgyptian.window_spectral_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:31:08.7096+00:00
-- url     : https://prove2.me/theorems/e9c725a5-ce5e-4b5e-ad04-4710ddd4f2eb
-- title:
--   High-frequency tail of products of interval character sums modulo $q$
-- statement:
--   Let $q\ge 1$ be an integer. For a residue $x\in\mathbb{Z}/q\mathbb{Z}$ write $\bar x\in\{0,1,\dots,q-1\}$ for its least nonnegative representative, let $e_q(x)=\exp(2\pi i\,\bar x/q)$ be the standard additive character of $\mathbb{Z}/q\mathbb{Z}$, and let $\|k\|_q=\min(\bar k,\;q-\bar k)$ be the distance of a frequency $k$ from $0$ around the cycle. For $L\in\mathbb{N}$ let $W_L=\{0,1,\dots,L-1\}\bmod q$ be the initial window of length $L$, and for a set $A\subseteq\mathbb{Z}/q\mathbb{Z}$ let $S_A(k)=\sum_{a\in A}e_q(ka)$ be its character sum.
--
--   Let $L$, $M$ and $H$ be natural numbers with $L\le q$, $M\le q$ and $H\ge 1$. Then
--
--   $$
--   \sum_{\substack{k\in\mathbb{Z}/q\mathbb{Z}\\ \|k\|_q>H}}\bigl|S_{W_L}(k)\bigr|\,\bigl|S_{W_M}(k)\bigr|\;\le\;\frac{2q^2}{H}.
--   $$
--
--   When one counts, by Fourier analysis on $\mathbb{Z}/q\mathbb{Z}$, how much mass a distribution puts on the sums $a+b$ with $a\in W_L$ and $b\in W_M$, the frequencies split into low and high ones; this estimate disposes of the high frequencies, uniformly in the window lengths. It is the high-frequency input of the window discrepancy estimate on $\mathbb{Z}/q\mathbb{Z}$.
--
--   **Formalization Note** The window is `natWindow q L`, the image of `Finset.range L` in `ZMod q`; the distance is `frequencyDistance k = min k.val (q - k.val)`; the character sum is `charSum A k`, the sum of `ZMod.stdAddChar (k * a)` over `a` in `A`. The instance `[NeZero q]` encodes $q\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/WindowSpectrum.lean#L132-L152

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

open OAI OAI.ShortEgyptian
universe uα uβ
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.window_spectral_tail {q L M : ℕ} [NeZero q] (hL : L ≤ q) (hM : M ≤ q)
    (H : ℕ) (hH : 1 ≤ H) :
    ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => H < frequencyDistance k),
      ‖charSum (natWindow q L) k‖ * ‖charSum (natWindow q M) k‖ ≤ 2 * (q : ℝ) ^ 2 / H := by sorry
