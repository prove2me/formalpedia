-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_independent_cover_of_packing_covering
-- name    : OAI.InfiniteMatroidCounterexample.independent_cover_of_packing_covering
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:47:28.568564+00:00
-- url     : https://prove2.me/theorems/cbb6c0d4-8281-4623-9273-f9c03d1e1636
-- title:
--   For self-dual matroids, a packing–covering decomposition yields a cover by two independent sets
-- statement:
--   Let $\alpha$ be a type and let $M_0,M_1$ be (possibly infinite) matroids on $\alpha$. For a matroid $M$ and $C\subseteq\alpha$ write $M|C$ for the restriction to $C$, $M^{*}$ for the dual, and
--   $$\operatorname{con}_C(M)=(M^{*}|C)^{*}$$
--   for the contraction of $M$ onto $C$ (the minor $M/(E(M)\setminus C)$, with ground set $C$). The pair $(M_0,M_1)$ has a *packing–covering decomposition* if there are sets $P,C,S_0,S_1,I_0,I_1\subseteq\alpha$ such that
--
--   1. $P\cap C=\emptyset$, $P\cup C=E(M_0)$, and $E(M_1)=E(M_0)$;
--   2. $S_0,S_1\subseteq P$, $S_0\cap S_1=\emptyset$, and $S_i$ is spanning in $M_i|P$ for $i=0,1$;
--   3. $I_0,I_1\subseteq C$, $I_i$ is independent in $\operatorname{con}_C(M_i)$ for $i=0,1$, and $I_0\cup I_1=C$.
--
--   **Theorem.** Suppose $E(M_0)=E(M_1)=\alpha$ and both matroids are self-dual, $M_0^{*}=M_0$ and $M_1^{*}=M_1$. If $(M_0,M_1)$ has a packing–covering decomposition, then there are an $M_0$-independent set $J_0$ and an $M_1$-independent set $J_1$ covering the ground set:
--   $$\exists\,J_0,J_1\subseteq\alpha:\qquad J_0\in\mathcal I(M_0),\quad J_1\in\mathcal I(M_1),\quad J_0\cup J_1=\alpha .$$
--
--   This is the reduction step of the main counterexample: for the constructed countable pair of self-dual matroids no $M_0$-independent set and $M_1$-independent set cover the ground set, so by this lemma the pair has no packing–covering decomposition. The lemma treats the general mixed decomposition, not only the pure packing ($C=\emptyset$) or pure covering ($P=\emptyset$) cases.
--
--   **Formalization Note** `HasPackingCovering M₀ M₁` is the existential statement in items 1 to 3, with `contractOnto M C = (M.dual ↾ C).dual` and spanning sets in the sense of Mathlib's `Matroid.Spanning`. Self-duality is the equation `M.dual = M` and the ground-set hypotheses are `M.E = univ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/PackingCovering.lean#L34-L57

import Mathlib
import Definitions.Def_InfiniteMatroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Basic
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BasisExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Zones
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Separation
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Prototype
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_PrototypeExtension
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_TransfiniteConstruction
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_RankDescent

open OAI OAI.InfiniteMatroidCounterexample
open Set Matroid

theorem OAI.InfiniteMatroidCounterexample.independent_cover_of_packing_covering {α : Type*} (M₀ M₁ : Matroid α)
    (hE₀ : M₀.E = univ) (hE₁ : M₁.E = univ) (hM₀ : M₀.dual = M₀) (hM₁ : M₁.dual = M₁)
    (h : HasPackingCovering M₀ M₁) :
    ∃ J₀ J₁ : Set α, M₀.Indep J₀ ∧ M₁.Indep J₁ ∧ J₀ ∪ J₁ = univ := by sorry
