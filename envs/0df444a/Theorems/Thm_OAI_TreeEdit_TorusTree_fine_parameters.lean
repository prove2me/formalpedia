-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusTree_fine_parameters
-- name    : OAI.TreeEdit.TorusTree.fine_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:14:10.091029+00:00
-- url     : https://prove2.me/theorems/ac7e0636-b369-4594-94ee-04999be15bcd
-- title:
--   Divisibility and size properties of the fine sampling modulus
-- statement:
--   Fix an integer $k\ge 2$ and write $m=16k^3$, $R=k^{8k}$ and $Q=k^{12k}$. Let $\mathcal P_k$ be the set of primes $p$ with $k^2<p\le k^3$, and let $j:\{0,1,\dots,16k-1\}\to\mathcal P_k$ be an injective map. For a permutation $\sigma$ of $\mathcal P_k$ define the period $\pi_\sigma=\prod_{u=0}^{16k-1}\sigma(j(u))$, the product of the $16k$ distinct primes selected by $\sigma\circ j$, and define the fine modulus
--   $$
--   M_j=R\cdot\Big(2Q\,\big((m+1)Q+1\big)\prod_{\sigma\in\mathrm{Sym}(\mathcal P_k)}\pi_\sigma\Big).
--   $$
--   Then:
--
--   1. $M_j>0$;
--   2. $2\mid M_j$;
--   3. $\pi_\sigma\mid M_j$ for every permutation $\sigma$ of $\mathcal P_k$;
--   4. $(m+1)\,Q<M_j$;
--   5. there are natural numbers $D,J$ with $D>0$, $M_j=R\,D$ and $M_j=J\,Q$.
--
--   The number $M_j$ is the modulus of the finite grid $\mathbb Z/M_j\mathbb Z\subset\mathbb R/\mathbb Z$ on which the circle-tree construction for the edit-distance lower bound is sampled. The five properties are exactly the arithmetic side conditions used later: evenness makes the half-turn $1/2$ a grid point, divisibility by every period makes every rotation step $1/\pi_\sigma$ a grid point, and the factorizations through $R$ and $Q$ together with $M_j>(m+1)Q$ are hypotheses of the Fourier displacement estimate.
--
--   **Formalization Note** In Lean, $m$, $R$, $Q$ are `branching k = 16*k*k^2`, `resolution k`, `cutoff k`; the pool is `Pool k` (primes of `PrimeSupply.band k 2`), $j$ is an embedding `Fin (16*k) ↪ Pool k`, $\pi_\sigma$ is `period poolPrime j σ` and $M_j$ is `fineModulus j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleObstruction.lean#L144-L165

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction

open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

theorem OAI.TreeEdit.TorusTree.fine_parameters {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k) :
    0 < fineModulus j ∧ 2 ∣ fineModulus j ∧
    (∀ σ : Equiv.Perm (Pool k), period poolPrime j σ ∣ fineModulus j) ∧
    (branching k+1)*cutoff k < fineModulus j ∧
    ∃ D J : ℕ, 0 < D ∧ fineModulus j = resolution k*D ∧ fineModulus j = J*cutoff k := by sorry
