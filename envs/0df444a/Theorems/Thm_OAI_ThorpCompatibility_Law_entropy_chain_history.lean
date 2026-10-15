-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_entropy_chain_history
-- name    : OAI.ThorpCompatibility.Law.entropy_chain_history
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:52:24.559281+00:00
-- url     : https://prove2.me/theorems/ed731d36-ca08-4239-9328-d97bca0fabb7
-- title:
--   Chain rule for conditional entropy along revealed histories
-- statement:
--   Let $\Omega,\mathcal X,\mathcal Y$ be finite sets, $P$ a probability distribution on $\Omega$, $n\in\mathbb N$, $X_0,\dots,X_{n-1}:\Omega\to\mathcal X$ random variables and $Y:\Omega\to\mathcal Y$ a further random variable. For $t\in\mathbb N$ let the *history* $X_{<t}$ be the random vector that records $X_0,\dots,X_{t-1}$ and marks the remaining coordinates as unrevealed: $X_{<t}(\omega)=(h_0,\dots,h_{n-1})$ with $h_i=X_i(\omega)$ for $i<t$ and $h_i=\ast$ (a symbol not in $\mathcal X$) for $i\ge t$. With the conditional Shannon entropy $H(U\mid V)=H(U,V)-H(V)$ of random variables under $P$,
--
--   $$
--   \sum_{i=0}^{n-1}H\big(X_i\,\big|\,Y,X_{<i}\big)\;=\;H\big((X_0,\dots,X_{n-1})\,\big|\,Y\big).
--   $$
--
--   This is the chain rule: the uncertainty of the whole vector given $Y$ is the sum of the uncertainties of its coordinates, each revealed in turn given $Y$ and the coordinates revealed before it. It is the form of the chain rule used in sequential exposure arguments, where an object is revealed one entry at a time on top of some side information $Y$.
--
--   **Formalization Note** The history is `history X t`, with values in functions `Fin n → Option β` (`none` marks an unrevealed coordinate), and the conditioning variable of the $i$-th term is the pair $(Y,X_{<i})$. All entropies are entropies of pushforward laws on finite types.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/EntropyChain.lean#L87-L115

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem OAI.ThorpCompatibility.Law.entropy_chain_history {n : ℕ} (P : Law α) (X : Fin n → α → β) (Y : α → γ) :
    (∑ i : Fin n, P.condEntropy (X i) (fun a => (Y a, history X i a))) =
      P.condEntropy (fun a i => X i a) Y := by sorry
