-- Prove2me | Theorems.Thm_OAI_TreeEdit_TorusFourier_branch_summaries
-- name    : OAI.TreeEdit.TorusFourier.branch_summaries
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:08:55.181561+00:00
-- url     : https://prove2.me/theorems/ea56ace3-7936-4681-a490-8f9cead449ee
-- title:
--   Low-frequency cycle-invariant characters are nontrivial on at least $K$ child diagonals
-- statement:
--   This is the number-theoretic branching step in the Fourier analysis of the random tree words used in the lower bound for the $\ell_1$ distortion of edit distance.
--
--   **Configurations.** Fix natural numbers $g, s, L, T$ and put $m = gs$. Let $I$ be a type, $r : I \to \mathbb{N}$, and an injective map $j : \{0,\dots,g-1\} \to I$. For a permutation $\sigma$ of $I$ let $P(\sigma) = \prod_{v=0}^{g-1} r(\sigma(j(v)))$. A child index $i \in \{0,\dots,m-1\}$ belongs to the group $\gamma(i) = \lfloor i/s \rfloor$; write $p_i(\sigma) = r(\sigma(j(\gamma(i))))$ and, for $z \in \mathbb{Z}/L$ with standard representative $\bar z$, put $c_\sigma(z,i) = 1 + (\bar z \bmod p_i(\sigma))\cdot \lfloor P(\sigma)/p_i(\sigma)\rfloor$. A configuration of depth $0$ is trivial, and a configuration of depth $h+1$ is a tuple $C = (\sigma, (z_i, C_i)_{i<m})$ consisting of a permutation $\sigma$ of $I$, residues $z_i \in \mathbb{Z}/L$ and configurations $C_i$ of depth $h$.
--
--   **States and cycle shifts.** Let $M \ge 1$, let $\mathcal{S}_0 = \mathbb{Z}/M$ and $\mathcal{S}_{h+1} = \mathcal{S}_h^{\,m}$ (labellings of the $m^h$ leaves of the complete $m$-ary tree of depth $h$, with coordinatewise addition), let $\Delta_h(u)$ be the constant state with all leaves equal to $u$, and let $\iota_i(y) \in \mathcal{S}_{h+1}$ be the state equal to $y \in \mathcal{S}_h$ at child $i$ and $0$ at the other children. For a configuration $C = (\sigma,(z_i,C_i))$ of depth $h+1$ the cycle shift $\kappa_C \in \mathcal{S}_{h+1}$ has $i$-th coordinate $\Delta_h\big(c_\sigma(z_i,i)\cdot\lfloor M/P(\sigma)\rfloor\big)$.
--
--   **Diagonal frequencies.** A character of a finite abelian group $G$ is a map $\chi : G \to \mathbb{C}$ with $\chi(0)=1$ and $\chi(x+y)=\chi(x)\chi(y)$. Every character $\psi$ of $\mathbb{Z}/M$ has the form $\psi(u) = e^{2\pi i k\bar u/M}$ for a unique $k \in \mathbb{Z}/M$; its centered frequency $\phi(\psi) \in \mathbb{Z}$ is the representative of $k$ with $-M < 2\phi(\psi) \le M$, so $\phi(\psi) = 0$ exactly when $\psi$ is trivial. For a character $\chi$ of $\mathcal{S}_h$ let $\chi^{\Delta}(u) = \chi(\Delta_h(u))$ be its diagonal summary, a character of $\mathbb{Z}/M$; for a character $\chi$ of $\mathcal{S}_{h+1}$ let $\chi_i(y) = \chi(\iota_i(y))$ be its restriction to child $i$, a character of $\mathcal{S}_h$.
--
--   **Statement.** Assume that every $r(v)$ is prime, $r$ is injective, $b \ge 1$ and $r(v) \ge b$ for all $v \in I$, $Q \le b^e$, $e + K \le g$ and $(gs+1)Q < M$. Let $C = (\sigma,(z_i,C_i))$ be a configuration of depth $h+1$ with $P(\sigma) \mid M$, and let $\chi$ be a character of $\mathcal{S}_{h+1}$ such that
--
--   - $|\phi(\chi^{\Delta})| < Q$, and $|\phi(\chi_i^{\Delta})| < Q$ for every child $i$;
--   - $\chi(\kappa_C) = 1$;
--   - $\chi^{\Delta}$ is not the trivial character.
--
--   Then
--
--   $$
--   K \le \#\big\{\, i \in \{0,\dots,m-1\} \;:\; \chi_i^{\Delta} \text{ is not trivial} \,\big\}.
--   $$
--
--   So a character that is nontrivial on the diagonal at a node, has only small diagonal frequencies at the node and at its children, and is invariant under the node's cycle shift, must be nontrivial on the diagonals of at least $K$ children. This branching phenomenon produces the factor $K^{-h}$ in the spectral mass bound for diagonal shifts.
--
--   **Formalization Note** The diagonal summary is `summary h χ`, the restriction to child $i$ is composition with `child h i`, the centered frequency is `centered`, and nontriviality of a character is expressed as being different from `0` in the additive group of characters. The type $I$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleFourier.lean#L278-L300

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

open OAI OAI.TreeEdit OAI.TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree

theorem OAI.TreeEdit.TorusFourier.branch_summaries {I : Type} {g s L M b e K Q : ℕ} [NeZero M] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r) (j : Fin g ↪ I)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQ : Q ≤ b^e) (hg : e+K ≤ g)
    (hM : (g*s+1)*Q < M) (h : ℕ) (C : Config I L (g*s) (h+1))
    (hPM : period r j C.1 ∣ M) (χ : AddChar (State (ZMod M) (g*s) (h+1)) ℂ)
    (hp : |(centered (summary (h+1) χ) : ℝ)| < Q)
    (hc : ∀ i : Fin (g*s), |(centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))) : ℝ)| < Q)
    (hχ : χ (cycle (M := M) r j h C) = 1) (hn : summary (h+1) χ ≠ 0) :
    K ≤ (Finset.univ.filter (fun i : Fin (g*s) => summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) ≠ 0)).card := by sorry
