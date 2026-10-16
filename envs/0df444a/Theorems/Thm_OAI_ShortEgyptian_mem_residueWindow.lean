-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_mem_residueWindow
-- name    : OAI.ShortEgyptian.mem_residueWindow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:31:41.308625+00:00
-- url     : https://prove2.me/theorems/47633ce4-7c4b-44b8-b523-b813b49ebdc0
-- title:
--   Membership criterion for the residue window $[0,\delta q)$ in $\mathbb{Z}/q\mathbb{Z}$
-- statement:
--   Let $q\ge1$ be an integer and let $\delta\le 1$ be a real number. For $x\in\mathbb{Z}/q\mathbb{Z}$ let $\bar x\in\{0,1,\dots,q-1\}$ be its least nonnegative representative. For real $y$ let $\lceil y\rceil_+$ denote the least natural number $m$ with $y\le m$ (so $\lceil y\rceil_+=0$ when $y\le0$), and define the residue window of relative length $\delta$ by
--   $$R_q(\delta)=\bigl\{\,n\bmod q:\ n\in\mathbb{N},\ n<\lceil\delta q\rceil_+\bigr\}\subseteq\mathbb{Z}/q\mathbb{Z}.$$
--   Then for every $x\in\mathbb{Z}/q\mathbb{Z}$,
--
--   $$
--   x\in R_q(\delta)\iff \bar x<\delta q .
--   $$
--
--   The window is defined as the image of an initial segment of integers, which is convenient for building it from smaller windows; this criterion translates membership into a plain inequality on representatives. The assumption $\delta\le1$ guarantees that the segment $\{0,\dots,\lceil\delta q\rceil_+-1\}$ does not wrap around modulo $q$. For $\delta\le0$ both sides are false.
--
--   **Formalization Note** The window is `residueWindow q δ = natWindow q ⌈δ * q⌉₊`, where `natWindow q L` is the image of `Finset.range L` in `ZMod q` and `⌈·⌉₊` is `Nat.ceil`; $\bar x$ is `x.val`, cast to a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/WindowDiscrepancy.lean#L119-L131

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

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.mem_residueWindow {q : ℕ} [NeZero q] {δ : ℝ} (hδ1 : δ ≤ 1) (x : ZMod q) :
    x ∈ residueWindow q δ ↔ (x.val : ℝ) < δ * q := by sorry
