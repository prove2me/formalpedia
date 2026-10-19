-- Prove2me | Theorems.Thm_OAI_FiniteCircle_mask_denominator_descent
-- name    : OAI.FiniteCircle.mask_denominator_descent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:40:43.716725+00:00
-- url     : https://prove2.me/theorems/6c70c76e-8947-4509-bc6b-52c1960cca0d
-- title:
--   Denominator descent: mask costs of nonzero phases supported on few primes are bounded below
-- statement:
--   **Setting.** Let $h,H,K,T$ be natural numbers and $M\ge1$, and let $p(j,k)$ ($j\in\mathbb{N}$, $0\le k<h$) be positive integers dividing $M$. Assume
--
--   * $T\ge2$, $2T\le h\le T^2$ and $K\ge2$;
--   * for $1\le j\le H$ and $k<h$, $p(j,k)$ is a prime with $h^3\le p(j,k)\le 2h^3$;
--   * primes at different levels differ: if $1\le j,r\le H$ and $j\ne r$, then $p(j,k)\ne p(r,k')$ for all $k,k'<h$.
--
--   With $\mathbb{Z}_n=\mathbb{Z}/n\mathbb{Z}$ and $\iota_{j,k}:\mathbb{Z}_{p(j,k)}\to\mathbb{Z}_M$, $a\mapsto(M/p(j,k))\,a$, the *mask costs* $c_l:\mathbb{Z}_M\to\mathbb{R}$ are $c_0(x)=\|x\|/M$ (with $\|x\|$ the circular distance from $x$ to $0$) and
--
--   $$
--   c_{l+1}(x)=\min_{z\in\prod_{k<h}\mathbb{Z}_{p(l+1,k)}}\frac1{t_{l+1}}\sum_{k<h}\sum_{b=0}^{p(l+1,k)-1}c_l\Bigl(x+\sum_{k'<h}\iota_{l+1,k'}(z_{k'})+b\,\iota_{l+1,k}(z_k)\Bigr),
--   $$
--
--   where $t_{l+1}=\sum_{k<h}p(l+1,k)$. A finite set $S\subset\mathbb{N}$ *supports* $x\in\mathbb{Z}_M$ if $\bigl(\prod_{q\in S}q\bigr)\,x=0$, and $S$ is *fresh below level $l$* if $p(j,k)\notin S$ for all $1\le j\le l$ and $k<h$. Finally let
--
--   $$
--   \beta(n,l)=\Bigl\lfloor\frac{n+lT+K-2}{K-1}\Bigr\rfloor,\qquad D(n,l)=\frac{1}{4^{l}\,T^{\,l+\beta(n,l)}\,h^{4K}}.
--   $$
--
--   **Theorem.** Let $l\le H$, let $S\subset\mathbb{N}$ be a finite set of at most $K$ primes, each at most $h^4$, which is fresh below level $l$, and let $x\in\mathbb{Z}_M$ be nonzero and supported by $S$. Then
--
--   $$
--   D(|S|,l)\le c_l(x).
--   $$
--
--   The set $S$ plays the role of a denominator of the phase $x$: it contains every prime factor of the additive order of $x$. The theorem says that a nonzero phase with a small denominator cannot have small mask cost, with a loss of a factor $4T$ per level plus a factor $T$ for each unit of the budget $\beta$. Together with the separation inequality for mask words, which bounds deficits from below by the costs $c_l$, this yields lower bounds on the deficits between mask words and their shifts.
--
--   **Formalization Note** "Supported" is `PhaseSupported S x`, "fresh below level $l$" is `LowerFresh h p l S`, $\beta$ is `resetBudget K T n l` (natural-number floor division; since $K\ge2$ no truncated subtraction occurs) and $D$ is `descentBound h K T n l`. The costs are `maskCost h p M hd hn l`, which require divisibility and positivity of $p(j,k)$ at every level $j$, whereas primality, the size bounds and distinctness are assumed only for $1\le j\le H$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/MaskDescent.lean#L148-L266

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

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.mask_denominator_descent {h H M K T : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hT : 2 ≤ T) (hhT : h ≤ T^2) (hTh : 2*T ≤ h) (hK : 2 ≤ K)
    (hd : ∀ j (k : Fin h), p j k ∣ M) (hn : ∀ j (k : Fin h), 0 < p j k)
    (hp : ∀ j, 1 ≤ j → j ≤ H → ∀ k : Fin h, (p j k).Prime)
    (hlo : ∀ j, 1 ≤ j → j ≤ H → ∀ k : Fin h, h^3 ≤ p j k)
    (hhi : ∀ j, 1 ≤ j → j ≤ H → ∀ k : Fin h, p j k ≤ 2*h^3)
    (hlevel : ∀ j r, 1 ≤ j → j ≤ H → 1 ≤ r → r ≤ H → j ≠ r →
      ∀ k t : Fin h, p j k ≠ p r t) :
    ∀ l, l ≤ H → ∀ (S : Finset ℕ) (x : ZMod M),
      S.card ≤ K → (∀ q ∈ S, q.Prime ∧ q ≤ h^4) → LowerFresh h p l S →
      x ≠ 0 → PhaseSupported S x →
      descentBound h K T S.card l ≤ maskCost h p M hd hn l x := by sorry
