-- Prove2me | Theorems.Thm_OAI_Paper320_towerFamily_blocks
-- name    : OAI.Paper320.towerFamily_blocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:06:10.310467+00:00
-- url     : https://prove2.me/theorems/16b01e93-dfe0-430c-a521-12bfb5490702
-- title:
--   Every function of the tower accepts the zero input with a lifted block flipped
-- statement:
--   Let $T$ be a tournament on $[k] = \{0, \dots, k-1\}$ with edge relation $i \to j$, let $r \ge 1$, and let $\lambda : [k] \times [k] \to [r]$ be any labeling. Let $I$ be a set, identify Boolean values with $\{0,1\}$, and let $\mathrm{base}$ assign to every $h \in \mathbb{N}$ a family $\mathrm{base}(h) = (\mathrm{base}(h)_0, \dots, \mathrm{base}(h)_{h-1})$ of $h$ Boolean functions on $\{0,1\}^I$. Recall the tower built from these data.
--
--   - **Coordinates.** $X_0 = I$ and $X_{n+1} = ([k] \times [r]) \times X_n$; an input $x$ on $X_{n+1}$ has children $x[j,c]$ on $X_n$, $x[j,c](a) = x((j,c),a)$.
--   - **Families.** $F^{(0,h)} = \mathrm{base}(h)$ and $F^{(n+1,h)} = \mathcal{R}\big(F^{(n,h+1)}\big)$, where $\mathcal{R}$ is one level of the row-clause construction over $(T,\lambda)$: for a family $G = (G_0, \dots, G_h)$, $\mathcal{R}(G)_q(x) = 1$ if and only if some row $i$ has all its children $x[i,c]$, $c \in [r]$, accepted by $G_h$ and all gate children $x[j,\lambda(i,j)]$ with $i \to j$ rejected by $G_{h-1-q}$. Thus $F^{(n,h)}$ consists of $h$ functions on $\{0,1\}^{X_n}$.
--   - **Blocks.** Given a set $K$ and finite blocks $B_b \subseteq I$ for $b \in K$, let $K_0 = K$ and $K_{n+1} = [k] \times K_n$, and define $B^{(0)}_b = B_b$ and $B^{(n+1)}_{(i,b)} = \mathrm{lift}_i\big(B^{(n)}_b\big)$, where $\mathrm{lift}_i(B) = \{ ((i,c),a) : c \in [r],\ a \in B \}$ places a copy of $B$ in every column of row $i$.
--
--   Write $\mathbf{0}$ for the all-zero input and $\mathbf{0}^{B}$ for the input obtained from $\mathbf{0}$ by flipping the coordinates in $B$, i.e. the indicator vector of $B$.
--
--   **Theorem.** Let $n, h \in \mathbb{N}$, and suppose that every member of $\mathrm{base}(h+n)$ rejects $\mathbf{0}$ and accepts every flipped base block:
--   $$
--   \mathrm{base}(h+n)_q(\mathbf{0}) = 0 \quad \text{and} \quad \mathrm{base}(h+n)_q\big(\mathbf{0}^{B_b}\big) = 1 \qquad \text{for all } q \in \{0, \dots, h+n-1\},\ b \in K.
--   $$
--   Then every member of the level-$n$ family $F^{(n,h)}$ accepts every flipped tower block:
--   $$
--   F^{(n,h)}_q\big(\mathbf{0}^{B^{(n)}_b}\big) = 1 \qquad \text{for all } b \in K_n,\ q \in \{0, \dots, h-1\}.
--   $$
--
--   Under the same hypotheses all members of the tower families reject $\mathbf{0}$, so each tower block is a sensitive block at the zero input for every function of the tower. Since lifting along the $k$ rows turns pairwise disjoint nonempty blocks into $k$ times as many pairwise disjoint nonempty blocks, this is how block sensitivity at the zero input is multiplied by $k$ at each level of the construction. No property of the labeling and no regularity of the tournament is needed.
--
--   **Formalization Note** The families are `towerFamily T label base n h`, the blocks are `towerBlocks blocks n b` with `b : TowerBlockIndex k K n` (nested pairs), and $\mathbf{0}^{B}$ is `flip (fun _ => false) B`. The sets $I$ and $K$ need not be finite. The assumption $r \ge 1$ is `0 < r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Tower.lean#L133-L155

import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower

open OAI OAI.Paper320
open scoped Classical

theorem OAI.Paper320.towerFamily_blocks {k r : ℕ} {I K : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (blocks : K → Finset I) (hr : 0 < r) (n h : ℕ)
    (hzero : ∀ q, base (h + n) q (fun _ => false) = false)
    (hblocks : ∀ b q, base (h + n) q (flip (fun _ => false) (blocks b)) = true) :
    ∀ b q, towerFamily T label base n h q
      (flip (fun _ => false) (towerBlocks blocks n b)) = true := by sorry
