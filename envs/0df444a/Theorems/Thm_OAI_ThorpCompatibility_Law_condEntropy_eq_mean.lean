-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_eq_mean
-- name    : OAI.ThorpCompatibility.Law.condEntropy_eq_mean
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:42:55.037913+00:00
-- url     : https://prove2.me/theorems/380d88f9-ef8b-4f70-b08d-b3cc66997471
-- title:
--   Conditional entropy as the expected conditional surprisal
-- statement:
--   Let $\Omega$, $\mathcal X$ and $\mathcal Y$ be finite sets, let $P$ be a probability distribution on $\Omega$, and let $X:\Omega\to\mathcal X$ and $Y:\Omega\to\mathcal Y$ be random variables. For a map $U$ on $\Omega$ write $P_U$ for its law (the pushforward $P_U(u)=\sum_{\omega:\,U(\omega)=u}P(\omega)$) and $H(U)=-\sum_uP_U(u)\log P_U(u)$ for its Shannon entropy. The conditional entropy is defined by $H(X\mid Y)=H(X,Y)-H(Y)$, where $H(X,Y)$ is the entropy of the joint law $P_{(X,Y)}$. For $\omega\in\Omega$ let $p(\omega)=P_{(X,Y)}\big(X(\omega),Y(\omega)\big)/P_Y\big(Y(\omega)\big)$ be the conditional probability, given the observed value of $Y$, of the observed value of $X$. Then
--
--   $$
--   H(X\mid Y)\;=\;-\sum_{\omega\in\Omega}P(\omega)\log\frac{P_{(X,Y)}\big(X(\omega),Y(\omega)\big)}{P_Y\big(Y(\omega)\big)}\;=\;-\,\mathbb E_P\big[\log p\big].
--   $$
--
--   The difference-of-entropies definition of $H(X\mid Y)$ is convenient for chain rules, while the expectation form is convenient for comparing the true conditional law with other predictors of $X$ from $Y$; this identity connects the two.
--
--   **Formalization Note** Division by zero and $\log 0$ follow Lean's conventions ($t/0=0$, $\log 0=0$); they only affect points $\omega$ with $P(\omega)=0$, which carry no weight.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/Entropy.lean#L115-L127

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem OAI.ThorpCompatibility.Law.condEntropy_eq_mean (P : Law α) (X : α → β) (Y : α → γ) :
    P.condEntropy X Y = -P.mean (fun a => Real.log (P.condMass X Y a)) := by sorry
