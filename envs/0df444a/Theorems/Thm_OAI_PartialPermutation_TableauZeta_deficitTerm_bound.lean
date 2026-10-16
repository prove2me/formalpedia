-- Prove2me | Theorems.Thm_OAI_PartialPermutation_TableauZeta_deficitTerm_bound
-- name    : OAI.PartialPermutation.TableauZeta.deficitTerm_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:43:25.579439+00:00
-- url     : https://prove2.me/theorems/6e0e8d39-31c8-43ad-b00d-6bed99e22403
-- title:
--   Diagrams with $n$ cells and deficit $k$ carry inverse tableau weight at most $2\,p(k)\,2^{u}\,2^{-uk/8}$
-- statement:
--   Throughout, a Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ (row $i$, column $j$) that is closed downwards: if $(i,j)\in\mu$, $i'\le i$ and $j'\le j$, then $(i',j')\in\mu$. Write $|\mu|$ for the number of cells, $\mu_1$ for the length of the first row and $\mu_1'$ for the length of the first column, and let
--
--   $$
--   \ell(\mu)=\max(\mu_1,\mu_1'),\qquad d(\mu)=|\mu|-\ell(\mu)
--   $$
--
--   be the length of a longest line and the deficit of $\mu$, i.e. the number of cells outside a longest row or column. Let $f^\mu$ be the number of standard Young tableaux of shape $\mu$, that is, of bijections from the cells of $\mu$ onto $\{1,\dots,|\mu|\}$ that strictly increase along every row and every column, and let $p(k)$ be the number of Young diagrams with $k$ cells. For $u\in\mathbb{R}$ and $n,k\in\mathbb{N}$ put
--
--   $$
--   w_u(\mu)=\begin{cases}0, & d(\mu)=0,\\ (f^\mu)^{-u}, & d(\mu)\ge 1,\end{cases}\qquad T_n(u,k)=\sum_{|\mu|=n,\ d(\mu)=k}w_u(\mu),
--   $$
--
--   where the sum runs over all Young diagrams with $n$ cells and deficit $k$.
--
--   **Theorem.** For all natural numbers $n$ and $k$ and every real number $u>0$,
--
--   $$
--   \big|T_n(u,k)\big|\le 2\,p(k)\,\exp\!\Big(u\log 2-\frac{u\log 2}{8}\,k\Big)=2^{1+u}\,p(k)\,2^{-uk/8}.
--   $$
--
--   The right-hand side does not depend on $n$, and as a function of $k$ it is summable (this is the separate result on the majorant $M_u(k)=2p(k)\exp(u\log 2-\frac{u\log 2}{8}k)$). Since $\sum_{k}T_n(u,k)=\sum_{|\mu|=n,\ d(\mu)\ge1}(f^\mu)^{-u}$, the bound is the domination hypothesis that allows the limit $n\to\infty$ to be taken term by term in $k$. The nonempty diagrams of deficit $0$ are exactly the single rows and single columns, which correspond to the trivial and sign representations of the symmetric group; since the irreducible representation of $S_n$ indexed by $\mu$ has dimension $f^\mu$, the estimate is a key step in showing that $\sum_{\pi}(\dim\pi)^{-u}$, over the irreducible representations $\pi$ of $S_n$, is bounded uniformly in $n$.
--
--   **Formalization Note** In Lean, $T_n(u,k)$ is `deficitTerm n u k`, a finite sum over the type `ShapeDeficit n k` of Young diagrams with $n$ cells whose deficit, written `card - max (rowLen 0) (colLen 0)`, equals $k$; $w_u$ is `inverseWeight u`, and the right-hand side is `majorant u k`. The count $f^\mu$ is `standardCount μ`, the number of strictly monotone bijections from the cells (ordered componentwise) onto `Fin |μ|`, and $(f^\mu)^{-u}$ is a real power. The norm on the left is the absolute value of a real number; since all weights are nonnegative it equals $T_n(u,k)$. The natural-number subtraction in $d(\mu)$ never truncates, because a line of $\mu$ has at most $|\mu|$ cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/TableauWeights.lean#L71-L89

import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DeficitCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauWeights

open OAI OAI.PartialPermutation OAI.PartialPermutation.TableauZeta
open Finset Filter
open Tableau DiagramCounting

theorem OAI.PartialPermutation.TableauZeta.deficitTerm_bound (n : ℕ) (u : ℝ) (hu : 0 < u) (k : ℕ) :
    ‖deficitTerm n u k‖ ≤ majorant u k := by sorry
