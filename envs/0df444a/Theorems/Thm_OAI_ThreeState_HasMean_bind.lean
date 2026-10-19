-- Prove2me | Theorems.Thm_OAI_ThreeState_HasMean_bind
-- name    : OAI.ThreeState.HasMean.bind
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:43:15.88639+00:00
-- url     : https://prove2.me/theorems/f3047cf6-004a-4b32-94c1-4fb32ecd027a
-- title:
--   Integrability under a composite law from integrability of the conditional absolute means
-- statement:
--   Let $p$ be a discrete probability distribution on a type $\alpha$. Let $k$ assign to each $a\in\alpha$ a discrete probability distribution $k_a$ on a type $\beta$, and let $f:\beta\to\mathbb{R}$. The composite law $p\gg\!=k$ first draws $a\sim p$ and then $b\sim k_a$, so that $(p\gg\!=k)(b)=\sum_{a}p(a)\,k_a(b)$. A function $g$ is integrable under a discrete law $q$ if $\sum_x q(x)|g(x)|<\infty$.
--
--   Assume:
--
--   1. $f$ is integrable under $k_a$ for every $a\in\alpha$;
--   2. the function $a\mapsto\mathbb{E}_{k_a}[|f|]=\sum_b k_a(b)|f(b)|$ is integrable under $p$.
--
--   Then $f$ is integrable under the composite law:
--   $$
--   \sum_{b\in\beta}\Bigl(\sum_{a\in\alpha}p(a)\,k_a(b)\Bigr)|f(b)|<\infty .
--   $$
--
--   This is the integrability half of the law of total expectation for discrete laws. It is used to control the moments of tree statistics, where the observation law is built by composing kernels.
--
--   **Formalization Note** Integrability is the predicate `HasMean`, i.e. summability of $x\mapsto q(x)g(x)$. For real families this is equivalent to absolute summability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Expectations.lean#L80-L100

import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations

open OAI OAI.ThreeState
open scoped Classical

theorem OAI.ThreeState.HasMean.bind {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) f)
    (hp : HasMean p (fun a => mean (k a) (fun b => |f b|))) :
    HasMean (p.bind k) f := by sorry
