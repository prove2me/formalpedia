-- Prove2me | Theorems.Thm_OptTwoSrcExt_lemma_4_1
-- name    : OptTwoSrcExt.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:42.948205+00:00
-- url     : https://prove2.me/theorems/8d0f8491-7e3d-4af7-bab2-92683fc156fc
-- title:
--   Lemma 4.1 — one-sided source-strong collision recycling, both retained sources
-- statement:
--   Let $X,Y$ be independent sources on $\{0,1\}^n$ with min-entropy at least $k$, put $K=2^k$, let $G:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^d$ be a seed function and $D=2^d$, let $E:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^p$ be a strong seeded extractor for min-entropy $k$ with error $\zeta$, $M=2^p$, and suppose $K\ge16M$. For $0<\theta<1$ let $\beta=3(1+\theta)\zeta/\theta+2\eta$ and
--   $$\mathcal B=\beta+\tfrac12\sqrt{\theta+2\beta+2(1+\theta)D^2\gamma+DM/K}.$$
--
--   1. If $G$ is one-sided non-malleable against every fixed-point-free left map at threshold $k-4$ with error $\gamma$, is an ordinary two-source extractor there with error $\gamma$, and $\Delta((X,G(X,Y)),(X,U_d))\le\eta$, then
--   $$\Delta\big((Y,G(X,Y),E(X,G(X,Y))),\,(Y,U_{d+p})\big)\le\mathcal B .\tag{4.1}$$
--   2. Symmetrically, if $G$ is one-sided non-malleable against every fixed-point-free right map at threshold $k-4$ with error $\gamma$, is an ordinary extractor there with error $\gamma$, and $\Delta((Y,G(X,Y)),(Y,U_d))\le\eta$, then $\Delta\big((X,G(X,Y),E(Y,G(X,Y))),(X,U_{d+p})\big)\le\mathcal B$.
--
--   The lemma recycles the entropy of $X$ left after the seed is computed: the payload $E(X,G(X,Y))$ is nearly uniform even given $Y$ and the seed, which is how the extractor of Theorem 1.5 reaches output length $2k-O(\log(1/\varepsilon))$.
--
--   **Formalization Note** Hypotheses (i) and (iii) quantify over all sources at their thresholds; hypothesis (ii) is about the given $X,Y$ only. $U_{d+p}$ is uniform on $\{0,1\}^d\times\{0,1\}^p$ and independent of the retained source.
--
--   Differences from the source:
--   - reading: The symmetric conclusion with X retained follows by exchanging the sources and using the right-tampering version of (i) → a second conjunct: right-tampering non-malleability, (ii) with Y retained, payload E(Y, G(X, Y)), X retained; reason: the printed exchange of the sources, stated explicitly (paper.md decision 9)
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Lemma 4.1, pp.80–81 (PDF pp.82–83)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_LowErrExt_IsTwoSourceExtractor
import Definitions.Def_OptTwoSrcExt_IsOneSidedNMLeft

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt

/-- **Lemma 4.1 (One-sided source-strong collision recycling), both conclusions.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Lemma 4.1, printed pp.80–81 (PDF pp.82–83): "Let X, Y be
independent n-bit sources of min-entropy at least k, put K = 2^k, let G be a d-bit seed, and put
D = 2^d. Suppose that (i) G is one-sided non-malleable against every fixed-point-free left map at
component threshold k − 4 with error γ, and is an ordinary extractor there with error γ; (ii) on the
current product law, ∆((X, G(X, Y)), (X, Ud)) ⩽ η; (iii) E : {0, 1}^n × {0, 1}^d → {0, 1}^p is a strong
seeded extractor at entropy k, with error ζ. Write M = 2^p, and suppose K ⩾ 16M. For 0 < θ < 1 let
β = 3(1 + θ)ζ/θ + 2η. Then ∆((Y, G(X, Y), E(X, G(X, Y))), (Y, Ud+p)) ⩽
β + ½ √(θ + 2β + 2(1 + θ)D²γ + DM/K). (4.1) The symmetric conclusion with X retained follows by
exchanging the sources and using the right-tampering version of (i)."

Let `X, Y` be independent sources on `{0,1}ⁿ` with min-entropy at least `k`, `G : {0,1}ⁿ × {0,1}ⁿ →
{0,1}^d`, `E : {0,1}ⁿ × {0,1}^d → {0,1}^p` a strong seeded extractor for min-entropy `k` with error `ζ`,
`2^k ≥ 16·2^p`, `0 < θ < 1`, `β = 3(1 + θ)ζ/θ + 2η`, `D = 2^d`, `M = 2^p`, `K = 2^k`, and
`B = β + ½ √(θ + 2β + 2(1 + θ)D²γ + DM/K)`.
1. If `G` is one-sided non-malleable against fixed-point-free left maps at threshold `k − 4` with
   error `γ`, is a two-source extractor there with error `γ`, and `Δ((X, G(X, Y)), (X, U_d)) ≤ η`, then
   `Δ((Y, G(X, Y), E(X, G(X, Y))), (Y, U_{d+p})) ≤ B`.
2. If `G` is one-sided non-malleable against fixed-point-free right maps at threshold `k − 4` with
   error `γ`, is a two-source extractor there with error `γ`, and `Δ((Y, G(X, Y)), (Y, U_d)) ≤ η`, then
   `Δ((X, G(X, Y), E(Y, G(X, Y))), (X, U_{d+p})) ≤ B`.

**Formalization Note.** Hypotheses (i) and (iii) quantify over all sources at their thresholds;
hypothesis (ii) concerns only the given `X, Y`. `k` is real and `D, M, K` are the powers `2^d, 2^p, 2^k`.
`U_{d+p}` is the uniform law on `{0,1}^d × {0,1}^p`, independent of the retained source. Clause 2 is
the printed "symmetric conclusion", with the right-tampering version of (i) (`IsOneSidedNMRight`)
and (ii) with `Y` retained. -/
theorem lemma_4_1 {n d p : ℕ} (k γ η ζ θ : ℝ) (X Y : PMF (Fin n → Bool))
    (hX : k ≤ minEntropy X) (hY : k ≤ minEntropy Y)
    (G : (Fin n → Bool) → (Fin n → Bool) → (Fin d → Bool))
    (E : (Fin n → Bool) → (Fin d → Bool) → (Fin p → Bool))
    (hE : IsStrongExtractor k ζ E) (hK : 16 * (2 : ℝ) ^ p ≤ (2 : ℝ) ^ k)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ((IsOneSidedNMLeft (k - 4) γ G ∧ IsTwoSourceExtractor (k - 4) γ G) →
      statDist ((indepPair X Y).map fun r => (r.1, G r.1 r.2))
          (indepPair X (PMF.uniformOfFintype (Fin d → Bool))) ≤ η →
      statDist ((indepPair X Y).map fun r => (r.2, G r.1 r.2, E r.1 (G r.1 r.2)))
          (indepPair Y (PMF.uniformOfFintype ((Fin d → Bool) × (Fin p → Bool)))) ≤
        (3 * (1 + θ) * ζ / θ + 2 * η) + 1 / 2 * Real.sqrt (θ + 2 * (3 * (1 + θ) * ζ / θ + 2 * η) +
          2 * (1 + θ) * ((2 : ℝ) ^ d) ^ 2 * γ + (2 : ℝ) ^ d * (2 : ℝ) ^ p / (2 : ℝ) ^ k)) ∧
    ((IsOneSidedNMRight (k - 4) γ G ∧ IsTwoSourceExtractor (k - 4) γ G) →
      statDist ((indepPair X Y).map fun r => (r.2, G r.1 r.2))
          (indepPair Y (PMF.uniformOfFintype (Fin d → Bool))) ≤ η →
      statDist ((indepPair X Y).map fun r => (r.1, G r.1 r.2, E r.2 (G r.1 r.2)))
          (indepPair X (PMF.uniformOfFintype ((Fin d → Bool) × (Fin p → Bool)))) ≤
        (3 * (1 + θ) * ζ / θ + 2 * η) + 1 / 2 * Real.sqrt (θ + 2 * (3 * (1 + θ) * ζ / θ + 2 * η) +
          2 * (1 + θ) * ((2 : ℝ) ^ d) ^ 2 * γ + (2 : ℝ) ^ d * (2 : ℝ) ^ p / (2 : ℝ) ^ k)) := by sorry

end OptTwoSrcExt
