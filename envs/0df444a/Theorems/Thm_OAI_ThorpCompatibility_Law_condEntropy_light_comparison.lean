-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_light_comparison
-- name    : OAI.ThorpCompatibility.Law.condEntropy_light_comparison
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:44:09.041651+00:00
-- url     : https://prove2.me/theorems/4f7a5ba7-f1ab-48ce-9049-4fb86cfd20b0
-- title:
--   Restricting a predictor to allowed light outcomes costs at most its excess log-loss
-- statement:
--   Let $\Omega,\mathcal X,\mathcal Y$ be finite sets, $P$ a probability distribution on $\Omega$, $X:\Omega\to\mathcal X$ and $Y:\Omega\to\mathcal Y$ random variables, and $K$ a predictor: for each $y\in\mathcal Y$ a probability distribution $K_y$ on $\mathcal X$. For $E\subseteq\mathcal X$ write $K_y(E)=\sum_{x\in E}K_y(x)$. Let $L,S\subseteq\mathcal Y\times\mathcal X$ be two relations, and for $y\in\mathcal Y$ put $L_y=\{x:(y,x)\in L\}$ (the *light* outcomes) and $S_y=\{x:(y,x)\in S\}$ (the *allowed* outcomes). Assume that for every $\omega$ with $P(\omega)>0$:
--
--   1. $K_{Y(\omega)}(X(\omega))>0$, and
--   2. $X(\omega)\in S_{Y(\omega)}$, i.e. the realized outcome is always allowed.
--
--   Define the *restriction cost* $c(\omega)=-\log\dfrac{K_{Y(\omega)}\big(L_{Y(\omega)}\cap S_{Y(\omega)}\big)}{K_{Y(\omega)}\big(L_{Y(\omega)}\big)}$ if $X(\omega)\in L_{Y(\omega)}$, and $c(\omega)=0$ otherwise. Then
--
--   $$
--   \mathbb E_P[c]\;\le\;-\,\mathbb E_P\big[\log K_Y(X)\big]\;-\;H(X\mid Y),
--   $$
--
--   where $H(X\mid Y)=H(X,Y)-H(Y)$ is the conditional Shannon entropy under $P$.
--
--   The right-hand side is the excess log-loss of the predictor $K$ over the true conditional law of $X$ given $Y$. The inequality says that the information gained, on light outcomes, by learning that the outcome is also allowed is paid for on average out of this excess. In the entropy analysis of compatible grids, $K$ predicts the next entry of a column from the previously revealed entries of that column, the light outcomes are those of small predicted probability, and the allowed outcomes are those not excluded by the rows and the previously exposed columns.
--
--   **Formalization Note** $L$ and $S$ are predicates `L S : γ → β → Prop`. At points with $P(\omega)>0$ and $X(\omega)\in L_{Y(\omega)}$ both probabilities in the ratio are positive; at all other points Lean's conventions ($t/0=0$, $\log 0=0$) may apply, but those points carry no weight or have cost $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/LightRescaling.lean#L122-L144

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem OAI.ThorpCompatibility.Law.condEntropy_light_comparison (P : Law α) (X : α → β) (Y : α → γ)
    (K : γ → Law β) (L S : γ → β → Prop)
    (hK : ∀ a, 0 < P.mass a → 0 < (K (Y a)).mass (X a))
    (hS : ∀ a, 0 < P.mass a → S (Y a) (X a)) :
    P.mean (fun a => if L (Y a) (X a) then
      -Real.log ((K (Y a)).prob (fun b => L (Y a) b ∧ S (Y a) b) /
        (K (Y a)).prob (L (Y a))) else 0) ≤
      -P.mean (fun a => Real.log ((K (Y a)).mass (X a))) - P.condEntropy X Y := by sorry
