-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_gibbs_le
-- name    : OAI.ThorpCompatibility.Law.gibbs_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:42:32.930192+00:00
-- url     : https://prove2.me/theorems/9d2b84cd-6ed4-4dba-950b-d2ab7997a510
-- title:
--   Gibbs variational inequality for a finite probability law
-- statement:
--   Let $\Omega$ be a finite set and let $P$ be a probability distribution on $\Omega$, given by masses $P(x)\ge0$ with $\sum_{x\in\Omega}P(x)=1$; write $\mathbb E_P[f]=\sum_x P(x)f(x)$. Let $a:\Omega\to\mathbb{R}$ satisfy $a(x)\ge0$ for all $x$ and $Z=\sum_{x\in\Omega}a(x)>0$, and suppose that $P$ vanishes wherever $a$ does: $a(x)=0\Rightarrow P(x)=0$. Then
--
--   $$
--   \mathbb E_P[\log a]-\sum_{x\in\Omega}P(x)\log P(x)\;\le\;\log\sum_{x\in\Omega}a(x).
--   $$
--
--   In terms of the Shannon entropy $H(P)=-\sum_x P(x)\log P(x)$ this reads $\mathbb E_P[\log a]+H(P)\le\log Z$: the energy-plus-entropy of any law that is absolutely continuous with respect to the weights $a$ is at most the log-partition function $\log Z$. It is the basic tool for comparing the expected log-weight of an arbitrary trial law with $\log Z$, for instance when bounding the expected log-weights of marginal laws by power means of the weights.
--
--   **Formalization Note** Logarithms follow Lean's convention $\log 0=0$, so terms with $P(x)=0$ contribute nothing; the hypothesis $a(x)=0\Rightarrow P(x)=0$ guarantees that no term $P(x)\log a(x)$ with $a(x)=0<P(x)$ occurs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/FiniteLaw.lean#L98-L119

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

theorem OAI.ThorpCompatibility.Law.gibbs_le (P : Law α) (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) (hs : ∀ x, a x = 0 → P.mass x = 0) :
    P.mean (fun x => Real.log (a x)) -
      (∑ x, P.mass x * Real.log (P.mass x)) ≤ Real.log (∑ x, a x) := by sorry
