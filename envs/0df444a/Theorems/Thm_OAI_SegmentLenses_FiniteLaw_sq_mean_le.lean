-- Prove2me | Theorems.Thm_OAI_SegmentLenses_FiniteLaw_sq_mean_le
-- name    : OAI.SegmentLenses.FiniteLaw.sq_mean_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:04:46.23665+00:00
-- url     : https://prove2.me/theorems/58160977-b684-4e9a-b293-2033542355ba
-- title:
--   The square of the mean is at most the mean of the square under a finite law
-- statement:
--   Let $\Omega$ be a finite set and let $\mu$ be a finite law on $\Omega$, that is, a weight function with $\mu(\omega)\ge0$ for every $\omega\in\Omega$ and $\sum_{\omega\in\Omega}\mu(\omega)=1$. The mean of $f:\Omega\to\mathbb{R}$ is $\mathbb{E}_\mu f=\sum_{\omega\in\Omega}\mu(\omega)\,f(\omega)$. For every $f:\Omega\to\mathbb{R}$,
--   $$
--   \big(\mathbb{E}_\mu f\big)^2\le\mathbb{E}_\mu\big(f^2\big).
--   $$
--
--   This is the nonnegativity of the variance, equivalently Jensen's inequality for the square function, for a probability distribution on a finite set. In the segment-norm estimates it is the basic tool for comparing squared means with means of squares. Examples are the bound $\mathbb{E}_\mu\sqrt{h}\le\sqrt{\mathbb{E}_\mu h}$ for $h\ge0$, and bounds on sums of squared averages by averaged energies.
--
--   **Formalization Note** `FiniteLaw Ω` is a structure with fields `weight`, `nonneg` and `total` over a `Fintype`, and `μ.mean f` is the weighted sum $\sum_\omega\mu(\omega)f(\omega)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/FiniteLaws.lean#L79-L91

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws

open OAI OAI.SegmentLenses OAI.SegmentLenses.FiniteLaw
open scoped BigOperators
open Finset
variable {Ω : Type*} [Fintype Ω]

theorem OAI.SegmentLenses.FiniteLaw.sq_mean_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.mean f ^ 2 ≤ μ.mean (fun ω => f ω ^ 2) := by sorry
