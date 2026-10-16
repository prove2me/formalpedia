-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_prod_mergeSamples
-- name    : OAI.ShortEgyptian.prod_mergeSamples
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:59:46.125482+00:00
-- url     : https://prove2.me/theorems/149b4590-7b44-4479-8ae9-b9708088d048
-- title:
--   Prime-label products of a merged sample split along a disjoint partition
-- statement:
--   Let $J$ be a finite set, $A$ any set, and $L,R\subseteq J$ disjoint subsets; write $C=J\setminus(L\cup R)$. Given maps $z:C\to A$, $x:L\to A$ and $y:R\to A$, let $z\sqcup x\sqcup y:J\to A$ be the merged map that agrees with $x$ on $L$, with $y$ on $R$ and with $z$ on $C$. Then for every function $p:A\to\mathbb N$,
--
--   $$
--   \prod_{j\in J}p\bigl((z\sqcup x\sqcup y)(j)\bigr)=\Bigl(\prod_{j\in C}p(z(j))\Bigr)\Bigl(\prod_{j\in L}p(x(j))\Bigr)\Bigl(\prod_{j\in R}p(y(j))\Bigr).
--   $$
--
--   In the random-prime model a sample $J\to A$ is decomposed into independent pieces on $C$, $L$ and $R$; this identity says that the product of the labels splits in the same way. It is what turns the phase of a product of random primes into a bilinear expression in the products over $L$ and over $R$.
--
--   **Formalization Note** The merged map is `mergeSamples L R z x y`, defined by cases (first $L$, then $R$, otherwise $C$); disjointness of $L$ and $R$ is what makes its restriction to $R$ equal to $y$. The products are taken in $\mathbb N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/SamplePartitions.lean#L59-L73

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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions

open OAI OAI.ShortEgyptian
universe uJ uA uE uM uK
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.ShortEgyptian.prod_mergeSamples {J : Type uJ} {A : Type uA} [Fintype J] (L R : Finset J) (hdis : Disjoint L R)
    (z : ((L∪R)ᶜ : Finset J) → A) (x : L → A) (y : R → A) (p : A → ℕ) :
    (∏ j, p (mergeSamples L R z x y j)) = (∏ j, p (z j))*(∏ j, p (x j))*(∏ j, p (y j)) := by sorry
