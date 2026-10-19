-- Prove2me | Theorems.Thm_OAI_ThreeState_mean_bind
-- name    : OAI.ThreeState.mean_bind
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:44:06.132704+00:00
-- url     : https://prove2.me/theorems/ad30c39c-88bf-4ea6-9e09-773c13126b8a
-- title:
--   Law of total expectation for a composite discrete law
-- statement:
--   Let $p$ be a discrete probability distribution on a type $\alpha$. Let $k$ assign to each $a\in\alpha$ a discrete probability distribution $k_a$ on a type $\beta$, and let $f:\beta\to\mathbb{R}$. The composite law $p\gg\!=k$ draws $a\sim p$ and then $b\sim k_a$, so $(p\gg\!=k)(b)=\sum_a p(a)k_a(b)$. Write $\mathbb{E}_q[g]=\sum_x q(x)g(x)$.
--
--   Assume:
--
--   1. $\sum_b k_a(b)|f(b)|<\infty$ for every $a$;
--   2. $\sum_a p(a)\,\mathbb{E}_{k_a}[|f|]<\infty$.
--
--   Then
--   $$
--   \mathbb{E}_{p\gg=k}[f]=\mathbb{E}_{a\sim p}\Bigl[\mathbb{E}_{k_a}[f]\Bigr],\qquad\text{i.e.}\qquad \sum_b\Bigl(\sum_a p(a)k_a(b)\Bigr)f(b)=\sum_a p(a)\sum_b k_a(b)f(b).
--   $$
--
--   This is the tower property for discrete laws, under an absolute-summability hypothesis. It is the basic tool for computing moments of observations defined by composing Markov kernels.
--
--   **Formalization Note** The hypotheses are the predicates `HasMean (k a) f` and `HasMean p (fun a => mean (k a) (fun b => |f b|))`. Expectations are real `tsum`s.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Expectations.lean#L102-L125

import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations

open OAI OAI.ThreeState
open scoped Classical

theorem OAI.ThreeState.mean_bind {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) f)
    (hp : HasMean p (fun a => mean (k a) (fun b => |f b|))) :
    mean (p.bind k) f = mean p (fun a => mean (k a) f) := by sorry
