-- Prove2me | Theorems.Thm_HyperKCut_Structure_claim_4_2
-- name    : HyperKCut.Structure.claim_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:15.59995+00:00
-- url     : https://prove2.me/theorems/5dc9b14a-57e4-4026-9f3c-f23ac965e229
-- title:
--   Claim 4.2 — the removed vertex lies on the sink side
-- statement:
--   In the proof of Theorem 1.2, choose $S\subseteq V_1$ with $|S|=2k-2$ maximizing the cut value of its source-maximal minimum $(S,T)$-terminal source set $V_S$. Choose $w\in V_1\setminus V_S$, set $C=S\cup\{w\}$, and for $u\in C$ let $B$ be the source-maximal minimum $((C\setminus\{u\}),T)$-terminal source set. Then
--
--   $$u\notin B.$$
--
--   This is Claim 4.2, with the paper's extremal choice and constructed sets made explicit as hypotheses.
--
--   **Formalization Note** The conclusion is the paper's $u\in\overline B$. The hypotheses are the setting of the paper's proof by contradiction: if Theorem 1.2 holds, no $S$ with the extremal property admits a vertex $w\in V_1\setminus V_S$, so the hypotheses cannot all hold. The claim is stated without the contrary assumption, exactly as its proof on p. 17 uses it, and its proof must argue directly from the extremal choice of $S$ and submodularity.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 17 (PDF 18), Claim 4.2 and its immediately preceding construction

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Claim 4.2, p. 17: each new terminal cut excludes the removed vertex. -/
theorem claim_4_2 (H : Hypergraph V) (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (P : Fin k → Finset V) (hP : IsMaximalMinKPartition H k P)
    (T : Finset V) (hT : T ⊆ (P 0)ᶜ)
    (hTj : ∀ j : Fin k, j ≠ 0 → (T ∩ P j).Nonempty)
    (S VS : Finset V) (hS : S ⊆ P 0) (hScard : S.card = 2 * k - 2)
    (hVS : IsSourceMaxMinTerminalCut H S T VS)
    (hmax : ∀ (X VX : Finset V), X ⊆ P 0 →
      X.card = 2 * k - 2 →
      IsSourceMaxMinTerminalCut H X T VX → d H VX ≤ d H VS)
    (w : V) (hw : w ∈ P 0 \ VS)
    (u : V) (hu : u ∈ insert w S)
    (B : Finset V)
    (hB : IsSourceMaxMinTerminalCut H ((insert w S).erase u) T B) :
    u ∉ B := by sorry

end HyperKCut.Structure
