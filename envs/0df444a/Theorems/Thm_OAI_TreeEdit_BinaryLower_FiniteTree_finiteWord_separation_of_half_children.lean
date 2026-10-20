-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_finiteWord_separation_of_half_children
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_separation_of_half_children
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:24:21.388997+00:00
-- url     : https://prove2.me/theorems/193c15c7-03e2-4624-8215-597ac6e62951
-- title:
--   Geometric deficit growth for finite-tree words
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Let $m\ge2$, $T\ge1$, and $\pi(p)$ the prefix periods with distinguished vectors $w(p)$. Assume the half-child condition: for every node $p$ of depth $<k$, rows $a,b<T$ and $t\in\mathbb Z$ with $\pi(p)\nmid t$, at least half of the children $i$ satisfy $\pi(p\,i)\nmid(b-a)+t\,L_{|p|}$. Then for every node $p$ of height $h$ (so $|p|+h=k$), state $x$ and $t$ with $\pi(p)\nmid t$,
--   $$
--   \frac{(mT)^h}{4^h}\le r_{(mT)^h}\bigl(\omega_h(p,x),\ \omega_h(p,x+t\,w(p))\bigr).
--   $$
--
--   A shift by a nonzero multiple of $w(p)$ costs a $4^{-h}$ fraction of the length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteSeparation.lean#L54-L120

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_separation_of_half_children {m k T : ℕ}
    (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (hm : 2 ≤ m) (hT : 0 < T)
    (hhalf : ∀ p (hp : p.length < k) (a b : Fin T) (t : ℤ),
      ¬ (wordPeriod primes i₀ p : ℤ) ∣ t →
      m ≤ 2 * (separatedChildren primes i₀ p hp a b t).card)
    (h : ℕ) (p : List (Fin m)) (hlen : p.length + h = k)
    (x : State (wordPeriods primes)) (t : ℤ)
    (ht : ¬ (wordPeriod primes i₀ p : ℤ) ∣ t) :
    (((m * T) ^ h : ℕ) : ℝ) / (4 : ℝ) ^ h ≤
      (deficit ((m * T) ^ h) (finiteWord primes i₀ T h p x)
        (finiteWord primes i₀ T h p (x + t • wordW primes i₀ p)) : ℝ) := by sorry
