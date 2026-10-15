-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_le_prediction
-- name    : OAI.ThorpCompatibility.Law.condEntropy_le_prediction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:43:44.075028+00:00
-- url     : https://prove2.me/theorems/2a93404d-4753-4d0c-8103-ae56a411cbdb
-- title:
--   Conditional entropy is at most the cross-entropy of any predictor
-- statement:
--   Let $\Omega,\mathcal X,\mathcal Y$ be finite sets, $P$ a probability distribution on $\Omega$, and $X:\Omega\to\mathcal X$, $Y:\Omega\to\mathcal Y$ random variables. Let $K$ be a *predictor* (a Markov kernel) from $\mathcal Y$ to $\mathcal X$: for each $y\in\mathcal Y$, $K_y$ is a probability distribution on $\mathcal X$. Assume that $K$ never assigns probability zero to an outcome that actually occurs, i.e. $K_{Y(\omega)}(X(\omega))>0$ for every $\omega$ with $P(\omega)>0$. Then
--
--   $$
--   H(X\mid Y)\;\le\;-\sum_{\omega\in\Omega}P(\omega)\log K_{Y(\omega)}\big(X(\omega)\big)\;=\;-\,\mathbb E_P\big[\log K_Y(X)\big],
--   $$
--
--   where $H(X\mid Y)=H(X,Y)-H(Y)$ is the conditional Shannon entropy, computed from the entropies of the laws of $(X,Y)$ and of $Y$ under $P$.
--
--   The right-hand side is the expected log-loss (cross-entropy) of predicting $X$ from $Y$ with the kernel $K$; the inequality says that no predictor does better than the true conditional distribution of $X$ given $Y$. It is the standard way to bound a conditional entropy from above by exhibiting an explicit, possibly simpler, prediction rule.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ConditionalEntropy.lean#L34-L64

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem OAI.ThorpCompatibility.Law.condEntropy_le_prediction (P : Law α) (X : α → β) (Y : α → γ)
    (K : γ → Law β) (hs : ∀ a, 0 < P.mass a → 0 < (K (Y a)).mass (X a)) :
    P.condEntropy X Y ≤ -P.mean (fun a => Real.log ((K (Y a)).mass (X a))) := by sorry
