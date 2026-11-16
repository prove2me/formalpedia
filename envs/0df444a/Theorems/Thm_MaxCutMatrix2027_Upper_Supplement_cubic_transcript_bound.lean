-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_cubic_transcript_bound
-- name    : MaxCutMatrix2027.Upper.Supplement.cubic_transcript_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:11:48.979513+00:00
-- url     : https://prove2.me/theorems/52e620a9-4304-42e4-8e03-5496f962d59c
-- title:
--   Lemma 7.5 — Cubic transcript bound
-- statement:
--   Let $n\ge2$, $0<\varepsilon\le1/160$, $\rho=40\varepsilon$, and fix a deterministic adaptive algorithm that always makes exactly $q$ distinct pair queries. Let $D_{1,T}$ and $D_{0,T}$ be the laws of its query transcript under the yes and no laws of Definition 5.1. Then, with KL in bits and $\log e=\log_2e$,
--   $$D_{\mathrm{KL}}(D_{1,T}\|D_{0,T})\le(\log e)\,e^2\left(\frac{104}{3}q\rho^4+\frac{256}{3}q^{3/2}\rho^5+\frac{512}{9}q^2\rho^6\right).$$
--
--   This is Eq. (47). It shows that $o(1/\rho^3)$ adaptive queries reveal little about the hidden partition, which yields the cubic adaptive lower bound.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: signs and edge indicators in {−1,1} (Y = −1 an edge) → Booleans (true ↦ sign 1; answer true = edge); reason: bijective relabeling; every quantity is transported unchanged
--   - encoding: the distributions D0, D1 and D1^joint of Definition 5.1 → explicit finite mass functions noLaw, yesLaw = ∑_σ yesJoint with yesJoint(σ,G) = 2^{-n} ∏_{u<v} Pr(Y_uv | σ); reason: these are exactly the product laws of Definition 5.1 and Eq. (35)
--   - encoding: a deterministic adaptive algorithm that always makes exactly q distinct queries, with E_t = f_t(T_{t−1}) → a finite decision tree QueryTree whose transcript on every graph has length q and pairwise distinct pairs (ExactlyDistinct q); reason: a decision tree is exactly a family of history-dependent query and output functions; the transcript T = T_q has q steps
--   - encoding: transcript distributions D_{1,T}, D_{0,T} and KL over the transcript space → push-forward mass functions transcriptLaw and a sum over the finite set of transcripts the tree can produce; reason: both laws vanish outside that set and D_{0,T} is positive on it, so the KL value is unchanged
--   - encoding: q^{3/2} → q·√q; reason: equal for every q ≥ 0
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma 7.5, p.37 (PDF p.37); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_QueryModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper.Supplement

/-- Lemma 7.5, p.37, Eq. (47): KL divergence (bits) between the yes and no transcript laws of
every deterministic adaptive tree that always makes exactly `q` distinct queries
(laws of Definition 5.1 with `ρ = 40ε`). -/
theorem cubic_transcript_bound (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 160) (q : ℕ) (T : QueryTree n) (hT : T.ExactlyDistinct q) :
    let ρ : ℝ := 40 * ε
    klOn (transcripts T) (transcriptLaw (fun G => yesLaw ρ G) T)
        (transcriptLaw (fun G => noLaw G) T) ≤
      log2e * Real.exp 1 ^ 2 *
        (104 / 3 * q * ρ ^ 4 + 256 / 3 * (q * Real.sqrt q) * ρ ^ 5 + 512 / 9 * q ^ 2 * ρ ^ 6) := by sorry

end MaxCutMatrix2027.Upper.Supplement
