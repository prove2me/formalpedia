-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_noHit_sum_variance
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_sum_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:12:45.203222+00:00
-- url     : https://prove2.me/theorems/5aec8951-4c53-4f18-a781-31971e779540
-- title:
--   Variance bound for a sum of avoidance indicators with bounded overlaps
-- statement:
--   Let $E$ be a finite set. A *configuration* is a function $s\colon E\to\{0,1\}$; read $s_e=1$ as "$e$ is selected". For a real number $p$ give each configuration the product weight $w_p(s)=\prod_{e\in E}p^{s_e}(1-p)^{1-s_e}$, and for a function $f\colon\{0,1\}^E\to\mathbb{R}$ write $\mathbb{E}_p[f]=\sum_{s\in\{0,1\}^E}w_p(s)\,f(s)$. When $0\le p\le1$ this is the expectation of $f$ when the coordinates $s_e$ are independent and each equals $1$ with probability $p$. For a set $A\subseteq E$ let $N_A(s)=\prod_{e\in A}(1-s_e)$, which is $1$ if no element of $A$ is selected and $0$ otherwise. Write $\operatorname{Var}_p(f)=\mathbb{E}_p\big[(f-\mathbb{E}_p[f])^2\big]$.
--
--   Let $0\le p\le1$, let $S$ be a finite index set, and for each $i\in S$ let $A_i\subseteq E$ be a "test set". Let $L$ and $K\ge0$ be real numbers such that
--
--   - every test set is small: $|A_i|\le L$ for all $i\in S$;
--   - every element of $E$ occurs in few tests: $|\{i\in S: e\in A_i\}|\le K$ for all $e\in E$.
--
--   Let $Y(s)=\sum_{i\in S}N_{A_i}(s)$ be the number of tests $i\in S$ in which nothing is selected. Then
--
--   $$
--   \operatorname{Var}_p(Y)=\mathbb{E}_p\big[(Y-\mathbb{E}_p[Y])^2\big]\le p\,|S|\,L\,K.
--   $$
--
--   This is a second-moment estimate for counts of objects that survive a random selection (for instance residual degrees, or the number of vertices not covered by selected edges). The variance is linear in $p$, in the number of tests, and in the bounds on the test sizes and on the multiplicity of each coordinate; combined with Chebyshev's inequality it shows that such counts concentrate around their means.
--
--   **Formalization Note** The tests are indexed by a `Finset` of an arbitrary type with decidable equality, and $Y$ is introduced by a `let`. Configurations are functions `E → Bool`; $w_p$, $\mathbb{E}_p$ and $N_A$ are `coinWeight p`, `expectation p` and `noHit A`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/ProductProbability.lean#L157-L214

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
universe uE uI
open scoped BigOperators
open Finset
variable {E : Type uE} [Fintype E] [DecidableEq E]

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_sum_variance {I : Type uI} [DecidableEq I] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset I) (A : I → Finset E)
    {K L : ℝ} (hK0 : 0 ≤ K) (hL : ∀ i ∈ S, ((A i).card : ℝ) ≤ L)
    (hK : ∀ e, ((S.filter fun i ↦ e ∈ A i).card : ℝ) ≤ K) :
    let Y : (E → Bool) → ℝ := fun s ↦ ∑ i ∈ S, noHit (A i) s
    expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) ≤
      p * S.card * L * K := by sorry
