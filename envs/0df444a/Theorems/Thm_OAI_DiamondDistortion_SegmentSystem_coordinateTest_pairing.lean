-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_coordinateTest_pairing
-- name    : OAI.DiamondDistortion.SegmentSystem.coordinateTest_pairing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:40:45.673084+00:00
-- url     : https://prove2.me/theorems/ca59e4ca-cd8d-4bde-90e4-5c51b5543681
-- title:
--   Pairing a dual functional with a finitely supported coordinate array
-- statement:
--   Let $\iota$ be a set and let $\mathcal{T}$ be a *segment system* on $\iota$: a distinguished collection of finite subsets of $\iota$, called *segments*, which contains every singleton $\{v\}$, $v\in\iota$ (nothing is assumed about the empty set). For a finitely supported function $u:\iota\to\mathbb{R}$, its *segment norm* is
--   $$
--   \|u\|_{\mathcal{T}}=\sup\Big\{\Big(\sum_{k=1}^{n}\Big(\sum_{v\in S_k}u(v)\Big)^2\Big)^{1/2}\ :\ n\in\mathbb{N},\ S_1,\dots,S_n\ \text{pairwise disjoint segments}\Big\}.
--   $$
--
--   Let $X_{\mathcal{T}}$ be the Banach space completion of the space of finitely supported functions $\iota\to\mathbb{R}$ under this norm, let $X_{\mathcal{T}}^*$ be its continuous dual, and let $j$ denote the canonical embedding of finitely supported functions into $X_{\mathcal{T}}$. For $v\in\iota$ let $e_v=j(\mathbf{1}_{\{v\}})\in X_{\mathcal{T}}$ be the unit vector at $v$.
--
--   Let $K\subseteq\iota$ be a finite set and $a:K\to\mathbb{R}$. Write $\tilde a:\iota\to\mathbb{R}$ for the extension of $a$ by zero ($\tilde a(v)=a(v)$ for $v\in K$ and $\tilde a(v)=0$ otherwise), which is finitely supported. Then for every $x\in X_{\mathcal{T}}^*$,
--   $$
--   x\big(j(\tilde a)\big)=\sum_{v\in K}a(v)\,x(e_v).
--   $$
--
--   Thus a continuous functional is determined, on vectors supported in a finite set $K$, by its values on the unit vectors $e_v$, $v\in K$. The identity converts local coordinate data on a finite set into dual pairings.
--
--   **Formalization Note** $\tilde a$ is `T.coordinateTest K a` (built with `Finsupp.onFinset`), $j$ is `T.finiteEmbedding`, $e_v$ is `T.unitVector v`, and $X_{\mathcal{T}}^*$ is `T.Dual`; the sum on the right runs over the subtype of elements of $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean#L792-L810

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
universe u v
open scoped BigOperators Classical Topology
open Set
variable {ι : Type*} (T : SegmentSystem ι)
variable {T}
variable (T)
variable {T}
variable (T)

theorem OAI.DiamondDistortion.SegmentSystem.coordinateTest_pairing (K : Finset ι) (a : T.Coordinates K) (x : T.Dual) :
    x (T.finiteEmbedding (T.coordinateTest K a)) =
      ∑ v : K, a v * x (T.unitVector v.val) := by sorry
