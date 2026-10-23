-- Prove2me | Theorems.Thm_LoockCVQEC_RepCode_syndrome_table
-- name    : LoockCVQEC.RepCode.syndrome_table
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:08.535056+00:00
-- url     : https://prove2.me/theorems/97b0ef38-d99a-4ffe-9ce8-07ca42606a19
-- title:
--   Sec. IV, p. 3 — the eight syndromes; only 'no error' and 'error in all three channels' coincide
-- statement:
--   Let $\bar x_2>0$. For a set $S\subseteq\{1,2,3\}$ of erring channels let $\sigma(S)\in\mathbb R^2$ be the displacement of ancilla modes 2 and 3 after decoding, i.e. the last two coordinates of $D\,\bar x_2\mathbf 1_S$ for the tritter matrix $D$. Then
--   $$\begin{aligned}&\sigma(\emptyset)=(0,0),\quad \sigma(\{1\})=\big(\sqrt{\tfrac23}\,\bar x_2,0\big),\quad \sigma(\{2\})=\big(-\tfrac{\bar x_2}{\sqrt6},\tfrac{\bar x_2}{\sqrt2}\big),\quad \sigma(\{3\})=\big(-\tfrac{\bar x_2}{\sqrt6},-\tfrac{\bar x_2}{\sqrt2}\big),\\ &\sigma(\{1,2\})=\big(\tfrac{\bar x_2}{\sqrt6},\tfrac{\bar x_2}{\sqrt2}\big),\quad \sigma(\{1,3\})=\big(\tfrac{\bar x_2}{\sqrt6},-\tfrac{\bar x_2}{\sqrt2}\big),\quad \sigma(\{2,3\})=\big(-\sqrt{\tfrac23}\,\bar x_2,0\big),\quad \sigma(\{1,2,3\})=(0,0),\end{aligned}$$
--   with the signs $(0,0),(+,0),(-,+),(-,-),(+,+),(+,-),(-,0),(0,0)$ the paper lists. Moreover, for all $S,T$,
--   $$\sigma(S)=\sigma(T)\iff S=T\ \text{ or }\ \{S,T\}=\{\emptyset,\{1,2,3\}\}.$$
--
--   So the only ambiguity in the syndrome is between no error and an error in every channel; every other pattern, including double errors, is identified.
--
--   **Formalization Note** Channel $j$ of the paper is Lean index $j-1$; `Finset.univ` is $\{1,2,3\}$.
--
--   Differences from the source:
--   - reading: the syndromes are listed by signs only: (0,0), (+,0), (−,+), (−,−), (+,+), (+,−), (−,0), (0,0) → the exact ancilla displacements (last two coordinates of D x̄₂1_S), whose signs are the listed ones for x̄₂ > 0; reason: the values are the ancilla shifts of Eq. (8); they determine the page's signs
--   - reading: "the only ambiguity" is all three errors vs no error; "all the other cases … can be identified" → σ(S) = σ(T) ↔ S = T ∨ {S, T} = {∅, univ}; reason: the precise content of the identification claim
--   - encoding: modes and channels numbered 1, 2, 3 → Fin 3, Lean index j − 1 for the paper's mode j; reason: Lean convention; same instances
-- source:
--   van Loock, A note on quantum error correction with continuous variables, arXiv:0811.3616v1, p. 3, Sec. IV ("The only ambiguity …", "The syndrome results …")

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

namespace LoockCVQEC.RepCode

open Real

theorem syndrome_table (d : ℝ) (hd : 0 < d) :
    (syndrome d ∅ = (0, 0)
      ∧ syndrome d {0} = (√(2 / 3) * d, 0)
      ∧ syndrome d {1} = (-(1 / √6 * d), 1 / √2 * d)
      ∧ syndrome d {2} = (-(1 / √6 * d), -(1 / √2 * d))
      ∧ syndrome d {0, 1} = (1 / √6 * d, 1 / √2 * d)
      ∧ syndrome d {0, 2} = (1 / √6 * d, -(1 / √2 * d))
      ∧ syndrome d {1, 2} = (-(√(2 / 3) * d), 0)
      ∧ syndrome d Finset.univ = (0, 0))
    ∧ ∀ S T : Finset (Fin 3), syndrome d S = syndrome d T ↔
        (S = T ∨ (S = ∅ ∧ T = Finset.univ) ∨ (S = Finset.univ ∧ T = ∅)) := by sorry

end LoockCVQEC.RepCode
