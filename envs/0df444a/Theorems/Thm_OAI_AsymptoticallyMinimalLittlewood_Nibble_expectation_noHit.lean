-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_expectation_noHit
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.expectation_noHit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:12:00.392789+00:00
-- url     : https://prove2.me/theorems/fd7b0335-fddc-481f-afb3-f67ab27d4afe
-- title:
--   Avoidance probability $(1-p)^{|A|}$ under independent Bernoulli selection
-- statement:
--   Let $E$ be a finite set. A *configuration* is a function $s\colon E\to\{0,1\}$; read $s_e=1$ as "$e$ is selected". For a real number $p$ give each configuration the product weight $w_p(s)=\prod_{e\in E}p^{s_e}(1-p)^{1-s_e}$, and for a function $f\colon\{0,1\}^E\to\mathbb{R}$ write $\mathbb{E}_p[f]=\sum_{s\in\{0,1\}^E}w_p(s)\,f(s)$. When $0\le p\le1$ this is the expectation of $f$ when the coordinates $s_e$ are independent and each equals $1$ with probability $p$. For a set $A\subseteq E$ let $N_A(s)=\prod_{e\in A}(1-s_e)$, which is $1$ if no element of $A$ is selected and $0$ otherwise.
--
--   For every real number $p$ and every subset $A\subseteq E$,
--
--   $$
--   \mathbb{E}_p[N_A]=(1-p)^{|A|}.
--   $$
--
--   In probabilistic language: if every element of $E$ is selected independently with probability $p$, then the probability that no element of $A$ is selected is $(1-p)^{|A|}$. As an identity between finite weighted sums it holds for every real $p$, with no restriction to $[0,1]$. It is the basic first-moment computation for counting objects that survive a random selection, and it underlies the covariance and mean estimates for sums of such indicators.
--
--   **Formalization Note** Configurations are functions `E → Bool` (`true` meaning selected); $w_p$, $\mathbb{E}_p$ and $N_A$ are `coinWeight p`, `expectation p` and `noHit A`, which are finite sums and products defined for every real $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/ProductProbability.lean#L119-L133

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

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.expectation_noHit (p : ℝ) (A : Finset E) :
    expectation p (noHit A) = (1 - p) ^ A.card := by sorry
