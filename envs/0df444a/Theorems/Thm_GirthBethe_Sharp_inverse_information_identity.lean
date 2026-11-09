-- Prove2me | Theorems.Thm_GirthBethe_Sharp_inverse_information_identity
-- name    : GirthBethe.Sharp.inverse_information_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:20:09.128188+00:00
-- url     : https://prove2.me/theorems/421a8f26-eeb8-4121-afbe-e4cea1dbebfd
-- title:
--   Lemma 5.4 — forward and inverse information gains have equal sums
-- statement:
--   Let $G=(L\sqcup R,E)$ be a finite bipartite graph, $\mu$ a probability law on its perfect matchings and $X:L\to R$ the matching bijection. For every $w\in R$,
--   $$\sum_{u\in L}I_\Gamma\big((X^{-1})_w;X_u\big)=\sum_{y\in R}I_\Gamma\big((X^{-1})_w;(X^{-1})_y\big).$$
--
--   The identity transfers Lemma 5.3, applied to $X^{-1}$, to information about right vertices gained from the forward coordinates.
--
--   Differences from the source:
--   - encoding: a bipartite graph G = (L ⊔ R, E) with |L| = |R| = n and its perfect matchings → finite types L, R, an edge finset E ⊆ L × R (a simple bipartite graph on L ⊕ R), and perfect matchings recorded as bijections σ : L ≃ R with (u, σ u) ∈ E for all u; |L| = |R| is not a separate hypothesis; reason: a perfect matching is the same as such a bijection; a probability law on perfect matchings exists only when one exists, which forces |L| = |R|
--   - encoding: a probability distribution μ on the perfect matchings, p_e = P(e ∈ M), X_u the partner of u → μ ∈ stdSimplex ℝ (PerfMatching E) (arbitrary, zeros allowed); p = edgeMarg μ, X_u = matchX u; reason: the same finite probability law and the same random variables
--   - generalization: the standing setting of §3: even g ≥ 4 and G of girth at least g → no hypothesis on g or on the girth of G; reason: the identity uses only that X is a bijection; adding the standing hypotheses gives the source statement
--   - encoding: L and R identified with [n] → L and R arbitrary finite types; Γ applied to laws on L; reason: the identification plays no role in the statement
--   - encoding: conditional laws given forward or inverse permutation coordinates in I_Γ → condLaw uses the unconditional law at probability-zero observations; reason: all such terms have weight zero in the defining expectations; the summed identity is unchanged
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 19, Lemma 5.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_MatchingLaw

open Finset

namespace GirthBethe.Sharp

/-- Lemma 5.4: `∑_{u ∈ L} I_Γ((X⁻¹)_w; X_u) = ∑_{y ∈ R} I_Γ((X⁻¹)_w; (X⁻¹)_y)` for every `w ∈ R`. -/
theorem inverse_information_identity {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R))
    (μ : PerfMatching E → ℝ) (hμ : μ ∈ stdSimplex ℝ (PerfMatching E)) (w : R) :
    ∑ u, infoGain gammaFun μ (matchXinv w) (matchX u) =
      ∑ y, infoGain gammaFun μ (matchXinv w) (matchXinv y) := by sorry

end GirthBethe.Sharp
