-- Prove2me | Theorems.Thm_OAI_FiniteCircle_expect_histDist_ofFn_ge
-- name    : OAI.FiniteCircle.expect_histDist_ofFn_ge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:24:08.04985+00:00
-- url     : https://prove2.me/theorems/ae3fc4ad-ed6e-47ee-8312-7e6f5c0a7ac7
-- title:
--   Expected histogram distance is at least $s$ when all cross-collisions together have probability at most $1/2$
-- statement:
--   Let $X$ be a set and $Y$ a finite set of labels. For a labelling $\ell:X\to Y$ and a finite sequence $\mathbf x=(x_1,\dots,x_s)$ of points of $X$, the *histogram* of $\mathbf x$ counts labels, $H_\ell(\mathbf x)(y)=\#\{r:\ \ell(x_r)=y\}$, and the *histogram distance* of two sequences is the $\ell^1$ distance of their histograms,
--   $$\operatorname{hd}_\ell(\mathbf x,\mathbf x')=\sum_{y\in Y}\bigl|H_\ell(\mathbf x)(y)-H_\ell(\mathbf x')(y)\bigr|.$$
--   Let $\mu$ be a finite probability law on a finite set $\Omega$ (nonnegative weights with total $1$, with expectation $\mathbb{E}_\mu$), and let $\omega\mapsto\operatorname{label}_\omega$ be a random labelling, that is, a map assigning to each $\omega\in\Omega$ a labelling $\operatorname{label}_\omega:X\to Y$.
--
--   **Theorem.** Let $s\in\mathbb{N}$, $f,g:\{0,\dots,s-1\}\to X$ and $p\in\mathbb{R}$. Assume that for all indices $i,j$
--   $$\mu\{\omega:\ \operatorname{label}_\omega(f(i))=\operatorname{label}_\omega(g(j))\}\le p,$$
--   and that $s^{2}p\le1/2$. Then
--
--   $$
--   s\ \le\ \mathbb{E}_{\omega\sim\mu}\Bigl[\operatorname{hd}_{\operatorname{label}_\omega}\bigl((f(0),\dots,f(s-1)),\,(g(0),\dots,g(s-1))\bigr)\Bigr].
--   $$
--
--   This is the lower-bound counterpart of the estimate for pointwise close sequences. If no entry of the first sequence is likely to share a label with any entry of the second, then with probability at least $1/2$ the two label multisets are disjoint and the histogram distance takes its maximal value $2s$. In the histogram embedding of edit distance it is applied, with $p=(s+1)^{-4}$, to the windows of two blocks whose deficit is large compared with the window scale $s$, and shows that the embedding does not contract distances.
--
--   **Formalization Note** The sequences are `List.ofFn f` and `List.ofFn g`, the histogram distance is `histDist (label ω)`, and the expectation is `μ.expect` for `μ : FiniteLaw Ω`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Histograms.lean#L197-L230

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

theorem OAI.FiniteCircle.expect_histDist_ofFn_ge {X Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) {s : ℕ} (f g : Fin s → X)
    (p : ℝ) (hp : ∀ i j, μ.event (fun ω => label ω (f i) = label ω (g j)) ≤ p)
    (hsp : (s : ℝ)^2 * p ≤ 1 / 2) :
    (s : ℝ) ≤ μ.expect (fun ω => histDist (label ω) (List.ofFn f) (List.ofFn g)) := by sorry
