-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_noHit_mean_error
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_mean_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:13:49.106546+00:00
-- url     : https://prove2.me/theorems/411a908d-bd4c-4d89-a336-2d9e94b31e48
-- title:
--   Mean of a sum of avoidance indicators for test sets of nearly equal size
-- statement:
--   Let $E$ be a finite set. A *configuration* is a function $s\colon E\to\{0,1\}$; read $s_e=1$ as "$e$ is selected". For a real number $p$ give each configuration the product weight $w_p(s)=\prod_{e\in E}p^{s_e}(1-p)^{1-s_e}$, and for a function $f\colon\{0,1\}^E\to\mathbb{R}$ write $\mathbb{E}_p[f]=\sum_{s\in\{0,1\}^E}w_p(s)\,f(s)$. When $0\le p\le1$ this is the expectation of $f$ when the coordinates $s_e$ are independent and each equals $1$ with probability $p$. For a set $A\subseteq E$ let $N_A(s)=\prod_{e\in A}(1-s_e)$, which is $1$ if no element of $A$ is selected and $0$ otherwise.
--
--   Let $0\le p\le1$ and let $M$, $B$ and $L\ge0$ be real numbers. Let $S$ be a finite index set and $A_i\subseteq E$ ($i\in S$) sets whose sizes are close to $M$ and bounded by $L$:
--   $\big||A_i|-M\big|\le B$ and $|A_i|\le L$ for all $i\in S$. Then
--
--   $$
--   \Big|\,\mathbb{E}_p\Big[\sum_{i\in S}N_{A_i}\Big]-|S|\,(1-pM)\Big|\le|S|\Big(pB+\frac{(pL)^2}{2}\Big).
--   $$
--
--   This is the first-moment companion of the variance bound for sums of avoidance indicators: the expected number of tests in which nothing is selected equals the linearized value $|S|(1-pM)$, up to an error caused by the spread $B$ of the test sizes and by the quadratic Bonferroni correction. It is used to compute expected residual degrees after a random selection of edges.
--
--   **Formalization Note** Configurations are functions `E → Bool` (`true` meaning selected); $w_p$, $\mathbb{E}_p$ and $N_A$ are `coinWeight p`, `expectation p` and `noHit A`, which are finite sums and products defined for every real $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/ProductProbability.lean#L262-L289

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

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.noHit_mean_error {I : Type uI} {p M B L : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hL : 0 ≤ L)
    (S : Finset I) (A : I → Finset E)
    (hcard : ∀ i ∈ S, |((A i).card : ℝ) - M| ≤ B)
    (hupper : ∀ i ∈ S, ((A i).card : ℝ) ≤ L) :
    |expectation p (fun s ↦ ∑ i ∈ S, noHit (A i) s) - S.card * (1 - p * M)| ≤
      S.card * (p * B + (p * L)^2 / 2) := by sorry
