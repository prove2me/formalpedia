-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusTree_good_halfturn_eventually
-- name    : OAI.TreeEdit.TorusTree.good_halfturn_eventually
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:13:08.4989+00:00
-- url     : https://prove2.me/theorems/372b227e-9c6f-4fa9-a4e6-232abe16ec5c
-- title:
--   For large $k$ some prime-pool configuration of depth $k$ is good for the half-turn
-- statement:
--   **Prime pool.** For a natural number $k$ let $\mathcal{P}_k$ be the set of primes $p$ with $k^2 < p \le k^3$, let $L_k = \prod_{p \in \mathcal{P}_k} p$, and put $\varepsilon_k = k^{-8k}$, $g = 16k$, $s = k^2$ and $m = gs = 16k^3$. For $t \in \mathbb{R}/\mathbb{Z}$ let $\|t\|$ be the distance from $t$ to the nearest integer.
--
--   **Configurations.** Fix an injective map $j : \{0,\dots,g-1\} \to \mathcal{P}_k$. For a permutation $\sigma$ of $\mathcal{P}_k$ let $P(\sigma) = \prod_{v=0}^{g-1}\sigma(j(v))$. A child index $i \in \{0,\dots,m-1\}$ belongs to the group $\gamma(i) = \lfloor i/s\rfloor$, with prime $p_i(\sigma) = \sigma(j(\gamma(i)))$, and for $z \in \mathbb{Z}/L_k$ with standard representative $\bar z$ put $c_\sigma(z,i) = 1 + (\bar z \bmod p_i(\sigma))\cdot P(\sigma)/p_i(\sigma)$. A configuration of depth $0$ is trivial, and a configuration of depth $h+1$ is $C = (\sigma,(z_i,C_i)_{i<m})$ with $\sigma$ a permutation of $\mathcal{P}_k$, $z_i \in \mathbb{Z}/L_k$ and configurations $C_i$ of depth $h$.
--
--   **Good rotations.** For a configuration $C$ of depth $h$ and $t \in \mathbb{R}/\mathbb{Z}$ define $\mathrm{Good}_h(C,t)$ recursively: $\mathrm{Good}_0(C,t)$ means $\|t\| \ge \varepsilon_k$, and for $C = (\sigma,(z_i,C_i))$ of depth $h+1$, $\mathrm{Good}_{h+1}(C,t)$ means that for every $a \in \{0,\dots,P(\sigma)-1\}$ at least a $1/64$ fraction of the children stay good after the rotation prescribed by $a$, namely $m \le 64\cdot\#\{i < m : \mathrm{Good}_h(C_i,\ t + a\,c_\sigma(z_i,i)/P(\sigma))\}$. Goodness depends on the choice of $j$.
--
--   **Theorem.** There is $k_0$ such that for every $k \ge k_0$ we have $k \ge 2$ and
--
--   $$
--   \exists\, j : \{0,\dots,16k-1\} \hookrightarrow \mathcal{P}_k \ \ \exists\, C \text{ of depth } k : \quad \mathrm{Good}_k\big(C,\ \tfrac12\big),
--   $$
--
--   where $j$ ranges over injective maps, $C$ over configurations with residues in $\mathbb{Z}/L_k$, and goodness is taken with threshold $\varepsilon_k$ and with respect to $j$.
--
--   Goodness of a rotation $t$ at depth $h$ is the hypothesis under which shifting all leaves by $t$ is shown to force a large edit deficit between the corresponding tree words. This result provides, for all large $k$, a concrete configuration of depth $k$ over the prime pool for which the half-turn $t = 1/2$ is good.
--
--   **Formalization Note** The phrase for all sufficiently large $k$ is the filter `atTop` on the natural numbers. The pool is the subtype `Pool k` of `PrimeSupply.band k 2` (the primes up to $k^3$ minus the primes up to $k^2$), the labelling of indices by primes is the inclusion `poolPrime`, $\varepsilon_k$ is the inverse of `resolution k` $= k^{8k}$, the branching $m$ is `branching k = 16 * k * k ^ 2`, which Lean matches with $g\cdot s$ for $g = 16k$ and $s = k^2$, and the half-turn is `point 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleObstruction.lean#L106-L127

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
open Classical Filter FiniteProbability

theorem OAI.TreeEdit.TorusTree.good_halfturn_eventually : ∀ᶠ k : ℕ in atTop, 2 ≤ k ∧
    ∃ (j : Fin (16 * k) ↪ Pool k) (C : Config (Pool k) (residueModulus k) (branching k) k),
      Good (resolution k : ℝ)⁻¹ poolPrime j k C (point 2) := by sorry
