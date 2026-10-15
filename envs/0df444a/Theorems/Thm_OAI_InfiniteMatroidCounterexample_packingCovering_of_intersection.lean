-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_packingCovering_of_intersection
-- name    : OAI.InfiniteMatroidCounterexample.packingCovering_of_intersection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:04:13.13884+00:00
-- url     : https://prove2.me/theorems/bdb3f065-f381-4113-bb51-157a5570d209
-- title:
--   The intersection property for $(M,N)$ implies the packing/covering property for $(M,N^*)$
-- statement:
--   Let $M$ and $N$ be matroids (in Mathlib's sense, so possibly infinite) on a common type $\alpha$. For a matroid $K$ on $\alpha$ write $E(K)$ for its ground set, $\operatorname{cl}_K$ for its closure operator, $K^*$ for its dual, $K|X$ for its restriction to $X\subseteq\alpha$ (a matroid with ground set $X$), and, for $C\subseteq\alpha$,
--   $$K.C=(K^*|C)^*$$
--   for the *contraction of $K$ onto $C$*; when $C\subseteq E(K)$ this is the contraction $K/(E(K)\setminus C)$, a matroid with ground set $C$.
--
--   - The pair $(M,N)$ has the **intersection property** if there are disjoint sets $J_0,J_1\subseteq\alpha$ such that $J=J_0\cup J_1$ is independent both in $M$ and in $N$ and
--   $$\operatorname{cl}_M(J_0)\cup\operatorname{cl}_N(J_1)=E(M).$$
--   - A pair $(M_0,M_1)$ of matroids on $\alpha$ has the **packing/covering property** if $E(M_1)=E(M_0)$ and there are sets $P,C,S_0,S_1,I_0,I_1\subseteq\alpha$ with: $P\cap C=\emptyset$ and $P\cup C=E(M_0)$; $S_0,S_1\subseteq P$, $S_0\cap S_1=\emptyset$, and $S_i$ is spanning in the restriction $M_i|P$ for $i=0,1$ (a packing of $P$); $I_0,I_1\subseteq C$, $I_i$ is independent in the contraction $M_i.C$ for $i=0,1$, and $I_0\cup I_1=C$ (a covering of $C$).
--
--   **Theorem.** Suppose $E(N)=E(M)$. If $(M,N)$ has the intersection property, then $(M,N^*)$ has the packing/covering property:
--
--   $$(M,N)\ \text{has the intersection property}\quad\Longrightarrow\quad(M,N^*)\ \text{has the packing/covering property}.$$
--
--   If $N$ is self-dual ($N^*=N$), the conclusion is the packing/covering property of $(M,N)$ itself. Contrapositively, a pair $(M,N)$ with common ground set and self-dual $N$ that fails the packing/covering property also fails the intersection property. This is how the counterexample transfers the failure of the packing/covering property for its two self-dual ray matroids on $\mathbb Z\times D$ to the failure of the intersection property.
--
--   **Formalization Note** The predicates are `HasIntersection M N`, i.e. `∃ J J₀ J₁, M.Indep J ∧ N.Indep J ∧ Disjoint J₀ J₁ ∧ J₀ ∪ J₁ = J ∧ M.closure J₀ ∪ N.closure J₁ = M.E`, and `HasPackingCovering M₀ M₁`, whose clauses are listed above in the same order; the contraction onto $C$ is `contractOnto M C = (M.dual ↾ C).dual` and the restriction is Mathlib's `M ↾ P`. The ground-set equation $E(M_1)=E(M_0)$ is part of the packing/covering predicate; here it reads $E(N^*)=E(M)$ and follows from the hypothesis `hE : N.E = M.E`. Mathlib's closure `M.closure X` is defined for every $X\subseteq\alpha$ and always lies in $E(M)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/IntersectionReduction.lean#L8-L59

import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries

open OAI OAI.InfiniteMatroidCounterexample
open Set Matroid

theorem OAI.InfiniteMatroidCounterexample.packingCovering_of_intersection {α : Type*} {M N : Matroid α}
    (hE : N.E = M.E) (h : HasIntersection M N) : HasPackingCovering M N.dual := by sorry
