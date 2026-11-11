-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_lemma_4_4
-- name    : NonMarkovColorings.Main.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:11:28.762425+00:00
-- url     : https://prove2.me/theorems/d65b65c8-7a4c-4b60-a638-850d6080a20d
-- title:
--   Lemma 4.4 — the local non-Markovian map is an involution: $\mathrm{NM}_{t,H^*}(\mathrm{NM}_{t,H^*}(\vec\sigma))=\vec\sigma$
-- statement:
--   Let $G$ have girth at least $7$, let $X_0,Y_0\in\widehat\Omega$ differ at exactly one vertex $z^*$, let $\vec\sigma\in(V\times[k])^{T_{cp}}$, and suppose $\mathrm{BC}(X_0,Y_0,\vec\sigma)=\mathrm{True}$ and the time $t$ satisfies Condition 3.5 with the fixed two-element set $H^*$. Then
--   $$\mathrm{NM}_{t,H^*}\big(\mathrm{NM}_{t,H^*}(\vec\sigma)\big)=\vec\sigma.$$
--   The second application recomputes all data ($\tau^\pm$, epochs, Ex, Avoid, $\alpha$, $\beta$, $B$) from its own input, with $H^*$ held fixed. This is the local half of the validity of the coupling: each local map is a bijection of update sequences, hence preserves the uniform law.
--
--   Differences from the source:
--   - generalization: standing assumptions of §3–5: Δ ≥ Δ0, k ≥ (1 + δ)Δ, C_cp large, one choice of the fixed orders → every graph with 7 ≤ egirth, every k, every C_cp ∈ ℕ, every choice of the four fixed orders; reason: §3.3–4.4 use only girth ≥ 7 and BC; the paper's setting is the special case
--   - encoding: times t ∈ [T] = {1, …, T} → index i : Fin T is time t = i + 1; X_{t−1} = run G X0 σ i; reason: Lean's Fin T is 0-based
--   - encoding: hypotheses BC(X0, Y0, σ) = True and Condition 3.5 → Cond35 G o Ccp X0 Y0 σ i H (whose second clause is BC); reason: Condition 3.5 contains BC as its first bullet; a separate hypothesis would be redundant
--   - encoding: NM_{t,H*} defined when Condition 3.5 holds → NM is a total function; reason: the statement assumes Condition 3.5 for σ; junk values are never involved in the hypothesis
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 26, Lemma 4.4

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_LabelingChain
import Definitions.Def_NonMarkovColorings_Main_BoundingChain
import Definitions.Def_NonMarkovColorings_Main_NonMarkovCoupling

namespace NonMarkovColorings.Main

/-- Lemma 4.4. If `X0, Y0` differ at exactly one vertex, `G` has girth `≥ 7`, and the time
`t = i + 1` satisfies Condition 3.5 for `(X0, Y0, σ)` with input set `H*` (which includes
`BC(X0, Y0, σ) = True`), then `NM_{t,H*}(NM_{t,H*}(σ)) = σ`. Stated for every `k`, every `C_cp`
and every choice of the fixed orders. -/
theorem lemma_4_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : 7 ≤ G.egirth) (k Ccp : ℕ) (o : Orders V) (X0 Y0 : V → Fin k)
    (hXY : (diffSet X0 Y0).card = 1) (σ : UpdSeq V k (Tcp V Ccp)) (i : Fin (Tcp V Ccp))
    (H : Finset (Fin k)) (hcond : Cond35 G o Ccp X0 Y0 σ i H) :
    NM G o Ccp X0 Y0 (NM G o Ccp X0 Y0 σ i H) i H = σ := by sorry

end NonMarkovColorings.Main
