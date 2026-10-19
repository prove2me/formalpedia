-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_exists_controlled_outcome
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.exists_controlled_outcome
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:14:34.330652+00:00
-- url     : https://prove2.me/theorems/0f051f0c-36d3-44a3-a8eb-8aa4a64baf40
-- title:
--   A configuration controlling many local deviations, one global deviation and a nonnegative count
-- statement:
--   Let $E$ be a finite set. A *configuration* is a function $s\colon E\to\{0,1\}$; read $s_e=1$ as "$e$ is selected". For a real number $p$ give each configuration the product weight $w_p(s)=\prod_{e\in E}p^{s_e}(1-p)^{1-s_e}$, and for a function $f\colon\{0,1\}^E\to\mathbb{R}$ write $\mathbb{E}_p[f]=\sum_{s\in\{0,1\}^E}w_p(s)\,f(s)$. When $0\le p\le1$ this is the expectation of $f$ when the coordinates $s_e$ are independent and each equals $1$ with probability $p$. Write $\operatorname{Var}_p(f)=\mathbb{E}_p\big[(f-\mathbb{E}_p[f])^2\big]$.
--
--   Let $0\le p\le1$. Let $U$ be a finite index set, let $Y_i$ ($i\in U$), $Z$ and $W$ be real-valued functions on $\{0,1\}^E$ with $W(s)\ge0$ for every $s$, let $V$, $V_Z$, $M$ be real numbers and let $t,b,u,c>0$. Assume
--
--   - $\operatorname{Var}_p(Y_i)\le V$ for every $i\in U$, and $\operatorname{Var}_p(Z)\le V_Z$;
--   - $\mathbb{E}_p[W]\le M$;
--   - $4\,|U|\,V\le t^2b$, $\;4V_Z\le u^2$ and $4M\le c$.
--
--   Then there is a configuration $s\in\{0,1\}^E$ such that simultaneously
--
--   $$
--   \Big|\big\{i\in U:\ |Y_i(s)-\mathbb{E}_p[Y_i]|>t\big\}\Big|\le b,\qquad|Z(s)-\mathbb{E}_p[Z]|\le u,\qquad W(s)\le c.
--   $$
--
--   The three numerical conditions make each of three "bad events" have probability at most $1/4$; the theorem packages Chebyshev's inequality, Markov's inequality and a union bound into a deterministic existence statement, with no randomness left in the conclusion. In a round of the nibble method it fixes a single selection of edges for which all but few residual degrees are close to their means, the number of uncovered vertices is close to its mean, and the number of collisions between selected edges is small.
--
--   **Formalization Note** The family $Y$ is indexed by an arbitrary type with decidable equality and $U$ is a `Finset` of it. Configurations are functions `E → Bool`, and $\mathbb{E}_p$ is the finite weighted sum `expectation p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/ProductProbability.lean#L323-L364

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

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.exists_controlled_outcome {I : Type uI} [DecidableEq I] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (U : Finset I)
    (Y : I → (E → Bool) → ℝ) (Z W : (E → Bool) → ℝ)
    {V Vz M t b u c : ℝ} (ht : 0 < t) (hb : 0 < b) (hu : 0 < u) (hc : 0 < c)
    (hY : ∀ i ∈ U, expectation p (fun s ↦ (Y i s - expectation p (Y i))^2) ≤ V)
    (hZ : expectation p (fun s ↦ (Z s - expectation p Z)^2) ≤ Vz)
    (hW0 : ∀ s, 0 ≤ W s) (hW : expectation p W ≤ M)
    (hV : 4 * U.card * V ≤ t^2*b) (hVz : 4*Vz ≤ u^2) (hM : 4*M ≤ c) :
    ∃ s, (((U.filter fun i ↦ t < |Y i s - expectation p (Y i)|).card : ℝ) ≤ b) ∧
      |Z s - expectation p Z| ≤ u ∧ W s ≤ c := by sorry
