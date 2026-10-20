-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteVectors_prefixPeriod_coprime_level
-- name    : OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_coprime_level
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:04:28.633827+00:00
-- url     : https://prove2.me/theorems/63e25bd4-c05f-4b8d-8843-8c4e4cd762de
-- title:
--   Prefix periods are coprime to deeper level products
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Fix positive integers $p(q,i)$ for levels $q<k$ and children $i<m$. Leaves are maps $a:\{0..k-1\}\to\{0..m-1\}$; $a,b$ agree to depth $j$ if $a_q=b_q$ for $q<j$. The prefix period is $\pi_j(a)=2\prod_{q<j}p(q,a_q)$, the leaf period $Q(a)=\pi_k(a)$, the level product $L_q=\prod_ip(q,i)$ and the suffix scale $s_j=\prod_{q\ge j}L_q$. Suppose the numbers $p(q,i)$ are pairwise distinct odd primes. Then for every $j<k$ and leaf $a$,
--   $$
--   \gcd\bigl(\pi_j(a),\,L_j\bigr)=1 .
--   $$
--
--   The period of a prefix shares no prime with the next level.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteVectors.lean#L269-L292

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteVectors
open scoped BigOperators
variable {m k : ℕ}

theorem OAI.TreeEdit.BinaryLower.FiniteVectors.prefixPeriod_coprime_level (p : Fin k → Fin m → ℕ)
    (hinj : Function.Injective (fun z : Fin k × Fin m => p z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (p q i)) (hodd : ∀ q i, p q i ≠ 2)
    (j : ℕ) (hj : j < k) (a : Leaf m k) :
    Nat.Coprime (prefixPeriod p j a) (levelProduct p ⟨j, hj⟩) := by sorry
