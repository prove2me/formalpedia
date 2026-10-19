-- Prove2me | Theorems.Thm_OAI_FiniteCircle_excluded_denominator_descent
-- name    : OAI.FiniteCircle.excluded_denominator_descent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:41:51.228986+00:00
-- url     : https://prove2.me/theorems/584ccd6d-8c0d-481c-9273-842656fcfbae
-- title:
--   Denominator descent: lower bound for the excluded-coordinate phase costs on $\mathbb{Z}/M$
-- statement:
--   Let $M\ge1$. For $x\in\mathbb{Z}/M$ let $\|x\|_M=|\tilde x|/M$, where $\tilde x\in(-M/2,M/2]$ is the integer representative of $x$ closest to $0$; thus $\|x\|_M$ is the distance from $x/M$ to the nearest integer. For a positive divisor $p$ of $M$ let $\iota_p:\mathbb{Z}/p\to\mathbb{Z}/M$, $a\mapsto (M/p)\,a$, be the embedding onto the subgroup of order $p$.
--
--   Fix natural numbers $m,H,K,T,B$ and positive integers $p_{l,k}$ ($l\in\mathbb{N}$, $0\le k<m$), each dividing $M$. The *excluded phase costs* $f_l:\mathbb{Z}/M\to\mathbb{R}$ are defined recursively by $f_0(x)=\|x\|_M$ and
--
--   $$
--   f_{l+1}(x)=\min_{z\in\prod_{k<m}\mathbb{Z}/p_{l+1,k}}\ \frac1m\sum_{i=0}^{m-1}f_l\Big(x+\sum_{j\ne i}\iota_{p_{l+1,j}}(z_j)\Big),
--   $$
--
--   so $x$ may be moved inside the subgroups attached to the level-$(l+1)$ moduli, but the $i$-th of the $m$ averaged terms omits the contribution of coordinate $i$. For $n,l\in\mathbb{N}$ put
--
--   $$
--   b(n,l)=\Big\lfloor\frac{n+lT+K-3}{K-2}\Big\rfloor,\qquad D(n,l)=\frac{1}{4^{l}\,B^{\,l+3b(n,l)}\,m^{5K}}.
--   $$
--
--   Assume:
--
--   1. $T\ge2$, $B\ge1$, $K\ge3$, $2T\le m$, $m\le B^4$ and $m\le TB$;
--   2. for every level $1\le l\le H$ the numbers $p_{l,0},\dots,p_{l,m-1}$ are pairwise distinct primes, each at most $m^5$;
--   3. moduli of different levels in $\{1,\dots,H\}$ never coincide: $p_{l,i}\ne p_{r,j}$ whenever $1\le l,r\le H$, $l\ne r$ and $0\le i,j<m$.
--
--   Then for every level $l\le H$, every finite set $S$ of primes such that $|S|\le K$, $q\le m^5$ for all $q\in S$, and $p_{j,k}\notin S$ for all $1\le j\le l$ and $0\le k<m$, and every nonzero $x\in\mathbb{Z}/M$ with $\big(\prod_{q\in S}q\big)\,x=0$,
--
--   $$
--   D(|S|,l)\le f_l(x).
--   $$
--
--   In words: a nonzero phase whose order is a product of at most $K$ primes of size at most $m^5$, fresh for the levels $1,\dots,l$, cannot be made cheap by $l$ rounds of averaged minimization; the bound loses a factor $4$ per level plus powers of $B$ controlled by the budget $b$. Applied at the top level with $S=\{2\}$ and $x=M/2$ (the half turn), it yields the lower bound on the excluded phase cost that drives the deficit estimate for the excluded-coordinate circle words.
--
--   **Formalization Note** $f_l$ is `excludedCost m p M hd hn l`, where `hd` and `hn` are the divisibility and positivity hypotheses; the condition $(\prod_{q\in S}q)\,x=0$ is `PhaseSupported S x`, the freshness condition is `LowerFresh m p l S`, $b(n,l)$ is `pairResetBudget K T n l` (natural-number floor division; $K-2>0$ here) and $D(n,l)$ is `pairDescentBound m K T B n l`. The hypotheses force $m\ge4$, so the averages are over a nonempty index set. For $l=0$ or $l>H$ the numbers $p_{l,k}$ are only required to be positive divisors of $M$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/ExcludedDescent.lean#L81-L200

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.excluded_denominator_descent {m H M K T B : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hT : 2 ≤ T) (hB : 1 ≤ B) (hmB : m ≤ B^4) (hmTB : m ≤ T*B)
    (hsmall : 2*T ≤ m) (hK : 3 ≤ K)
    (hd : ∀ l (k : Fin m), p l k ∣ M) (hn : ∀ l (k : Fin m), 0 < p l k)
    (hp : ∀ l, 1 ≤ l → l ≤ H → ∀ k : Fin m, (p l k).Prime)
    (hin : ∀ l, 1 ≤ l → l ≤ H → ∀ k : Fin m, p l k ≤ m^5)
    (hinj : ∀ l, 1 ≤ l → l ≤ H → Function.Injective (fun k : Fin m => p l k))
    (hlevel : ∀ l r, 1 ≤ l → l ≤ H → 1 ≤ r → r ≤ H → l ≠ r →
      ∀ i j : Fin m, p l i ≠ p r j) :
    ∀ l, l ≤ H → ∀ (S : Finset ℕ) (x : ZMod M), S.card ≤ K →
      (∀ q ∈ S, q.Prime ∧ q ≤ m^5) → LowerFresh m p l S → x ≠ 0 →
      PhaseSupported S x → pairDescentBound m K T B S.card l ≤ excludedCost m p M hd hn l x := by sorry
