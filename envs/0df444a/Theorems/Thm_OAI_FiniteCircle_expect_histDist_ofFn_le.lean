-- Prove2me | Theorems.Thm_OAI_FiniteCircle_expect_histDist_ofFn_le
-- name    : OAI.FiniteCircle.expect_histDist_ofFn_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:23:06.326251+00:00
-- url     : https://prove2.me/theorems/a0d184be-be8a-46e5-9846-4195f3a2d4e8
-- title:
--   Expected histogram distance is at most $2sp$ when corresponding points are separated with probability at most $p$
-- statement:
--   Let $X$ be a set and $Y$ a finite set of labels. For a labelling $\ell:X\to Y$ and a finite sequence $\mathbf x=(x_1,\dots,x_s)$ of points of $X$, the *histogram* of $\mathbf x$ counts labels, $H_\ell(\mathbf x)(y)=\#\{r:\ \ell(x_r)=y\}$, and the *histogram distance* of two sequences is the $\ell^1$ distance of their histograms,
--   $$\operatorname{hd}_\ell(\mathbf x,\mathbf x')=\sum_{y\in Y}\bigl|H_\ell(\mathbf x)(y)-H_\ell(\mathbf x')(y)\bigr|.$$
--   Let $\mu$ be a finite probability law on a finite set $\Omega$ (nonnegative weights with total $1$, with expectation $\mathbb{E}_\mu$), and let $\omega\mapsto\operatorname{label}_\omega$ be a random labelling, that is, a map assigning to each $\omega\in\Omega$ a labelling $\operatorname{label}_\omega:X\to Y$.
--
--   **Theorem.** Let $s\in\mathbb{N}$, let $f,g:\{0,\dots,s-1\}\to X$ and $p\in\mathbb{R}$, and assume that for every index $i$
--   $$\mu\{\omega:\ \operatorname{label}_\omega(f(i))\ne\operatorname{label}_\omega(g(i))\}\le p.$$
--   Then
--
--   $$
--   \mathbb{E}_{\omega\sim\mu}\Bigl[\operatorname{hd}_{\operatorname{label}_\omega}\bigl((f(0),\dots,f(s-1)),\,(g(0),\dots,g(s-1))\bigr)\Bigr]\ \le\ 2sp.
--   $$
--
--   If two sequences are close entry by entry, in the sense that the random labelling rarely separates corresponding entries, then their label histograms are close in expectation. In the histogram embedding of edit distance the two sequences are the windows of two words that differ by one local move, and this inequality bounds how far the move can displace the embedding.
--
--   **Formalization Note** The sequences are `List.ofFn f` and `List.ofFn g`, the histogram distance is `histDist (label ω)`, and the expectation is `μ.expect` for `μ : FiniteLaw Ω`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Histograms.lean#L177-L195

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem OAI.FiniteCircle.expect_histDist_ofFn_le {X Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) {s : ℕ} (f g : Fin s → X)
    (p : ℝ) (hp : ∀ i, μ.event (fun ω => label ω (f i) ≠ label ω (g i)) ≤ p) :
    μ.expect (fun ω => histDist (label ω) (List.ofFn f) (List.ofFn g)) ≤ 2 * s * p := by sorry
