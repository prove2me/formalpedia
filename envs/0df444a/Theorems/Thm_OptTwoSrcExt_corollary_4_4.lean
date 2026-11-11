-- Prove2me | Theorems.Thm_OptTwoSrcExt_corollary_4_4
-- name    : OptTwoSrcExt.corollary_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:30.121976+00:00
-- url     : https://prove2.me/theorems/c4610fc3-d8e6-4c4c-9d6e-3702aa651930
-- title:
--   Corollary 4.4 — appending the second payload: error $\xi+\zeta_R$
-- statement:
--   Let $X,Y$ be independent sources on $\{0,1\}^n$, $S=G(X,Y)$ a $d$-bit seed computed from them, $E_L:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^p$ and $E_R:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^q$. Suppose the left payload satisfies the conclusion of Lemma 4.1 with distance bound $\xi$,
--   $$\Delta\big((Y,S,E_L(X,S)),\,(Y,U_d,U_p)\big)\le\xi,$$
--   and $E_R$ is a strong seeded extractor with error $\zeta_R$ at a min-entropy threshold that $Y$ meets. Then
--   $$\Delta\big((S,E_L(X,S),E_R(Y,S)),\,U_{d+p+q}\big)\le\xi+\zeta_R .\tag{4.4}$$
--
--   This is the last step of the construction of Theorem 1.5: the output $(S,E_L(X,S),E_R(Y,S))$ retains the seed and both payloads.
--
--   Differences from the source:
--   - reading: Assume Lemma 4.1 for the left payload of length p, and let its distance bound be ξ → the hypothesis Δ((Y, S, E_L(X, S)), (Y, U_d, U_p)) ≤ ξ; reason: the conclusion of Lemma 4.1 is exactly what the proof uses (pp.84–85; paper.md decision 10)
--   - reading: ER is a strong seeded extractor for Y → IsStrongExtractor at a threshold k_R with k_R ≤ H∞(Y); reason: "for Y" means Y meets the extractor's entropy threshold
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Corollary 4.4, p.84 (PDF p.86)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt

/-- **Corollary 4.4 (Ordinary concatenation from one-payload recycling).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Corollary 4.4, printed p.84 (PDF p.86): "Assume Lemma 4.1
for the left payload of length p, and let its distance bound be ξ. If ER is a strong seeded extractor
for Y with q output bits and error ζR, then ∆((S, EL(X, S), ER(Y, S)), Ud+p+q) ⩽ ξ + ζR. (4.4)"

Let `X, Y` be independent sources on `{0,1}ⁿ`, `S = G(X, Y)` a `d`-bit seed computed from them,
`E_L : {0,1}ⁿ × {0,1}^d → {0,1}^p` and `E_R : {0,1}ⁿ × {0,1}^d → {0,1}^q`. If
`Δ((Y, S, E_L(X, S)), (Y, U_d, U_p)) ≤ ξ` (the conclusion of Lemma 4.1 for the left payload), and `E_R`
is a strong seeded extractor with error `ζ_R` for min-entropy `k_R ≤ H∞(Y)`, then
`Δ((S, E_L(X, S), E_R(Y, S)), U_{d+p+q}) ≤ ξ + ζ_R`.

**Formalization Note.** "Assume Lemma 4.1 for the left payload … let its distance bound be ξ" is read
as the hypothesis that the comparison (4.1) holds with bound `ξ`, which is what the proof uses
(pp.84–85). "Strong seeded extractor for Y" is the published `FuzzyExtractors.Hamming.IsStrongExtractor`
at a threshold `k_R` that `Y` meets. `U_{d+p+q}` is the uniform law on `{0,1}^d × {0,1}^p × {0,1}^q`;
`U_d, U_p` in the hypothesis are uniform on `{0,1}^d × {0,1}^p` and independent of `Y`. -/
theorem corollary_4_4 {n d p q : ℕ} (ξ ζR kR : ℝ) (X Y : PMF (Fin n → Bool))
    (G : (Fin n → Bool) → (Fin n → Bool) → (Fin d → Bool))
    (EL : (Fin n → Bool) → (Fin d → Bool) → (Fin p → Bool))
    (ER : (Fin n → Bool) → (Fin d → Bool) → (Fin q → Bool))
    (hL : statDist ((indepPair X Y).map fun r => (r.2, G r.1 r.2, EL r.1 (G r.1 r.2)))
        (indepPair Y (PMF.uniformOfFintype ((Fin d → Bool) × (Fin p → Bool)))) ≤ ξ)
    (hER : IsStrongExtractor kR ζR ER) (hY : kR ≤ minEntropy Y) :
    statDist ((indepPair X Y).map fun r => (G r.1 r.2, EL r.1 (G r.1 r.2), ER r.2 (G r.1 r.2)))
        (PMF.uniformOfFintype ((Fin d → Bool) × (Fin p → Bool) × (Fin q → Bool))) ≤
      ξ + ζR := by sorry

end OptTwoSrcExt
