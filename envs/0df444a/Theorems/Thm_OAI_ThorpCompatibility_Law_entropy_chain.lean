-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_entropy_chain
-- name    : OAI.ThorpCompatibility.Law.entropy_chain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:52:48.505855+00:00
-- url     : https://prove2.me/theorems/bf5342c6-01b4-48cd-b42a-d96aed768932
-- title:
--   Chain rule for the entropy of a random vector
-- statement:
--   Let $\Omega$ and $\mathcal X$ be finite sets, $P$ a probability distribution on $\Omega$, $n\in\mathbb N$, and $X_0,\dots,X_{n-1}:\Omega\to\mathcal X$ random variables. For $t\in\mathbb N$ let $X_{<t}$ be the history that records $X_0,\dots,X_{t-1}$ and marks the coordinates $i\ge t$ as unrevealed. With the Shannon entropy $H$ of laws under $P$ and the conditional entropy $H(U\mid V)=H(U,V)-H(V)$,
--
--   $$
--   \sum_{i=0}^{n-1}H\big(X_i\,\big|\,X_{<i}\big)\;=\;H(X_0,\dots,X_{n-1}).
--   $$
--
--   This is the chain rule for entropy: the entropy of a random vector is the sum of the conditional entropies of its coordinates, each given the previously revealed ones. In the analysis of compatible grids it splits the entropy of a random column permutation into the contributions of its entries, revealed one at a time.
--
--   **Formalization Note** The history is `history X t`, with values in functions `Fin n → Option β` (`none` marks an unrevealed coordinate); the right-hand side is the entropy of the law of $\omega\mapsto(X_i(\omega))_{i<n}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/EntropyChain.lean#L117-L131

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

theorem OAI.ThorpCompatibility.Law.entropy_chain {n : ℕ} (P : Law α) (X : Fin n → α → β) :
    (∑ i : Fin n, P.condEntropy (X i) (history X i)) =
      (P.map (fun a i => X i a)).entropy := by sorry
