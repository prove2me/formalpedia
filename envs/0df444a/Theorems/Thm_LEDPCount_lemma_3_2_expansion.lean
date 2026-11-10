-- Prove2me | Theorems.Thm_LEDPCount_lemma_3_2_expansion
-- name    : LEDPCount.lemma_3_2_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:18.497835+00:00
-- url     : https://prove2.me/theorems/76b18dad-7e74-42aa-987f-40af406054c6
-- title:
--   Proof of Lemma 3.2 — per-injection expansion of $\beta$
-- statement:
--   Fix an injection $\phi:V(H)\hookrightarrow[n]$ and write $E=E(H)$. For all symmetric real matrices $A$ and $Z$,
--   $$
--   \begin{aligned}
--   &\frac{1}{|\mathrm{Aut}(H)|}\Bigl(\prod_{e\in E}(A_{\phi(e)}+Z_{\phi(e)})-\sum_{e\in E}Z_{\phi(e)}\prod_{e'\in E\setminus\{e\}}(A_{\phi(e')}+Z_{\phi(e')})-\prod_{e\in E}A_{\phi(e)}\Bigr)\\
--   &=\frac{1}{|\mathrm{Aut}(H)|}\Bigl(\sum_{\emptyset\ne S\subseteq E}\prod_{e\in S}Z_{\phi(e)}\prod_{e'\in E\setminus S}A_{\phi(e')}-\sum_{e\in E}\ \sum_{\{e\}\subseteq S\subseteq E}\prod_{e'\in S}Z_{\phi(e')}\prod_{e''\in E\setminus S}A_{\phi(e'')}\Bigr)\\
--   &=\frac{1}{|\mathrm{Aut}(H)|}\sum_{\emptyset\ne S\subseteq E}(1-|S|)\prod_{e\in S}Z_{\phi(e)}\prod_{e'\in E\setminus S}A_{\phi(e')}.
--   \end{aligned}
--   $$
--   In the proof, $Z=X-A$ is the randomized-response error, and the left side is $\phi$'s contribution to $\beta$; the terms with $|S|=1$ cancel.
--
--   Differences from the source:
--   - generalization: A the {0,1}-valued adjacency matrix and Z = X − A → arbitrary real A and Z; reason: the identity is polynomial algebra; it specializes to the source's A and Z
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), proof of Lemma 3.2, p.19–20 (PDF p.21–22)

import Mathlib
import Definitions.Def_LEDPCount_autCount

namespace LEDPCount

/-- Proof of Lemma 3.2, per-injection expansion (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.19–20, PDF p.21–22): fix an
injection `ϕ : V(H) ↪ [n]` and write `E = E(H)`. Its contribution to `β`,
`|Aut(H)|⁻¹ (∏_{e∈E}(A + Z)_{ϕ(e)} − ∑_{e∈E} Z_{ϕ(e)} ∏_{e'∈E∖{e}} (A + Z)_{ϕ(e')} − ∏_{e∈E} A_{ϕ(e)})`,
equals `|Aut(H)|⁻¹ (∑_{∅≠S⊆E} ∏_{S} Z ∏_{E∖S} A − ∑_{e∈E} ∑_{{e}⊆S⊆E} ∏_{S} Z ∏_{E∖S} A)`,
which equals `|Aut(H)|⁻¹ ∑_{∅≠S⊆E} (1 − |S|) ∏_{e∈S} Z_{ϕ(e)} ∏_{e∈E∖S} A_{ϕ(e)}`.

**Formalization Note** Stated for arbitrary real matrices `A`, `Z` (functions on unordered
pairs); the paper's `A` is {0,1}-valued. -/
theorem lemma_3_2_expansion {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) {n : ℕ} (A Z : Sym2 (Fin n) → ℝ) (ϕ : Fin k ↪ Fin n) :
    (autCount H : ℝ)⁻¹ *
        (∏ e ∈ H.edgeFinset, (A (e.map ϕ) + Z (e.map ϕ)) -
          ∑ e ∈ H.edgeFinset, Z (e.map ϕ) *
            ∏ e' ∈ H.edgeFinset.erase e, (A (e'.map ϕ) + Z (e'.map ϕ)) -
          ∏ e ∈ H.edgeFinset, A (e.map ϕ)) =
      (autCount H : ℝ)⁻¹ *
        (∑ S ∈ H.edgeFinset.powerset.filter (fun S => S.Nonempty),
            (∏ e ∈ S, Z (e.map ϕ)) * ∏ e ∈ H.edgeFinset \ S, A (e.map ϕ) -
          ∑ e ∈ H.edgeFinset, ∑ S ∈ H.edgeFinset.powerset.filter (fun S => e ∈ S),
            (∏ e' ∈ S, Z (e'.map ϕ)) * ∏ e' ∈ H.edgeFinset \ S, A (e'.map ϕ)) ∧
    (autCount H : ℝ)⁻¹ *
        (∑ S ∈ H.edgeFinset.powerset.filter (fun S => S.Nonempty),
            (∏ e ∈ S, Z (e.map ϕ)) * ∏ e ∈ H.edgeFinset \ S, A (e.map ϕ) -
          ∑ e ∈ H.edgeFinset, ∑ S ∈ H.edgeFinset.powerset.filter (fun S => e ∈ S),
            (∏ e' ∈ S, Z (e'.map ϕ)) * ∏ e' ∈ H.edgeFinset \ S, A (e'.map ϕ)) =
      (autCount H : ℝ)⁻¹ *
        ∑ S ∈ H.edgeFinset.powerset.filter (fun S => S.Nonempty),
          (1 - (S.card : ℝ)) * (∏ e ∈ S, Z (e.map ϕ)) * ∏ e ∈ H.edgeFinset \ S, A (e.map ϕ) := by sorry

end LEDPCount
