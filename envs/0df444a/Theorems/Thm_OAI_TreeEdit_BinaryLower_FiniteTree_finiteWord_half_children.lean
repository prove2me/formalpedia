-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_finiteWord_half_children
-- name    : OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_half_children
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:07:57.914981+00:00
-- url     : https://prove2.me/theorems/0cd16690-eaa6-499b-9b31-4e6414ceff87
-- title:
--   Half of the children separate two rows in the finite tree
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Fix positive integers $p(q,i)$ for levels $q<k$ and children $i<m$. Leaves are maps $a:\{0..k-1\}\to\{0..m-1\}$; $a,b$ agree to depth $j$ if $a_q=b_q$ for $q<j$. The prefix period is $\pi_j(a)=2\prod_{q<j}p(q,a_q)$, the leaf period $Q(a)=\pi_k(a)$, the level product $L_q=\prod_ip(q,i)$ and the suffix scale $s_j=\prod_{q\ge j}L_q$. Here $m=20k$, $k\ge2$, the $p(q,i)$ are distinct primes at least $k^4$, $p$ is a node with $|p|<k$, and $\pi(\cdot)$ denotes word prefix periods. Let $a,b<k^{20k}$ be rows and $t\in\mathbb Z$ with $\pi(p)\nmid t$. Then
--   $$
--   20k\le2\,\bigl|\{i:\ \pi(p\,i)\nmid(b-a)+t\,L_{|p|}\}\bigr| .
--   $$
--
--   This is the half-child condition of the geometric induction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteWordPrimeSeparation.lean#L37-L76

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.FiniteTree.finiteWord_half_children {k : ℕ} (hk : 2 ≤ k)
    (primes : Fin k → Fin (20 * k) → ℕ) (i₀ : Fin (20 * k))
    (p : List (Fin (20 * k))) (hp : p.length < k)
    (hinj : Function.Injective
      (fun z : Fin k × Fin (20 * k) => primes z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (primes q i))
    (hlarge : ∀ q i, k ^ 4 ≤ primes q i)
    (a b : Fin (k ^ (20 * k))) (t : ℤ)
    (ht : ¬ (wordPeriod primes i₀ p : ℤ) ∣ t) :
    20 * k ≤ 2 * (Finset.univ.filter fun i : Fin (20 * k) =>
      ¬ (wordPeriod primes i₀ (p ++ [i]) : ℤ) ∣
        (b : ℤ) - (a : ℤ) +
          t * (FiniteVectors.levelProduct primes ⟨p.length, hp⟩ : ℤ)).card := by sorry
