-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_mean_predict
-- name    : OAI.ThorpCompatibility.Law.mean_predict
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:48:53.333596+00:00
-- url     : https://prove2.me/theorems/42b88295-df0a-43f4-b744-b8dcbabd4814
-- title:
--   Tower property for conditional prediction laws
-- statement:
--   Let $\Omega,\mathcal X,\mathcal Y$ be finite sets, $P$ a probability distribution on $\Omega$, and $X:\Omega\to\mathcal X$, $Y:\Omega\to\mathcal Y$ random variables. For $y\in\mathcal Y$ let $\widehat P_y$ be the *prediction law* of $X$ given $Y=y$: if $P(Y=y)>0$ it is the conditional law $\widehat P_y(x)=P(X=x\mid Y=y)$, and if $P(Y=y)=0$ it is, by convention, the law of $X$ under $P$. Then for every function $f:\mathcal Y\times\mathcal X\to\mathbb{R}$,
--
--   $$
--   \sum_{\omega\in\Omega}P(\omega)\sum_{x\in\mathcal X}\widehat P_{Y(\omega)}(x)\,f\big(Y(\omega),x\big)\;=\;\sum_{\omega\in\Omega}P(\omega)\,f\big(Y(\omega),X(\omega)\big),
--   $$
--
--   that is, $\mathbb E_P\big[\mathbb E_{x\sim\widehat P_Y}[f(Y,x)]\big]=\mathbb E_P[f(Y,X)]$.
--
--   This is the tower property (law of total expectation) for the finite conditional laws of the entropy calculus: averaging a quantity over the predicted value of $X$ given $Y$, and then over $Y$, gives the same result as evaluating it at the actual value of $X$.
--
--   **Formalization Note** The prediction law is `P.predict X Y y`, the pushforward under $X$ of `P.restrict (fun a => Y a = y)`; the restriction of $P$ to an event of probability zero is defined to be $P$ itself. Such $y$ never occur as values $Y(\omega)$ with $P(\omega)>0$, so this convention does not affect the identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/Prediction.lean#L74-L106

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem OAI.ThorpCompatibility.Law.mean_predict (P : Law α) (X : α → β) (Y : α → γ) (f : γ → β → ℝ) :
    P.mean (fun a => (P.predict X Y (Y a)).mean (f (Y a))) =
      P.mean (fun a => f (Y a) (X a)) := by sorry
