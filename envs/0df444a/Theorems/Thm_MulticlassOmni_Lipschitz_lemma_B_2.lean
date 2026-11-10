-- Prove2me | Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_2
-- name    : MulticlassOmni.Lipschitz.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:10:40.975225+00:00
-- url     : https://prove2.me/theorems/b10cab96-ee75-472e-9251-f6e92c4e8a9c
-- title:
--   Lemma B.2 — sphere packing in the simplex with coordinate bounds (144), radius (145) and separation (146)
-- statement:
--   There are absolute constants $C_{\mathrm{pack}},\varepsilon_0>0$ such that, for every integer $k\ge3$ and every $0<\varepsilon\le\varepsilon_0$, there is a finite set $X=\{x_1,\dots,x_N\}\subseteq\Delta_k$ with $N\ge2^{-C_{\mathrm{pack}}k}\varepsilon^{-(k-2)/2}$ (143) such that, with $\bar v=(1/k,\dots,1/k)$, for all $i$ and $y$: $\tfrac7{8k}\le(x_i)_y\le\tfrac9{8k}$ and $(x_i)_1\le\tfrac{15}{16k}$ (144); $\|x_i-\bar v\|_2^2=\tfrac1{256k}$ (145); and $\langle x_i-\bar v,x_j-\bar v\rangle\le\tfrac{1-8000\varepsilon}{256k}$ for $i\ne j$ (146). The conclusion is `IsSimplexPacking Cpack k ε X`.
--
--   Differences from the source:
--   - encoding: labels [k] = {1, …, k} → Fin k, the source label y is the index y − 1 (label 1 is index 0); reason: relabeling; same instances
--   - encoding: X = {x_1, …, x_N} with N ≥ … → a Finset X with (X.card : ℝ) ≥ …; reason: same object
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Lemma B.2, p. 55

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings

namespace MulticlassOmni.Lipschitz

/-- **Lemma B.2 (Sphere packing in the simplex)**, Hu, Luo, Schneider, Yang (2026), p. 55.
There are absolute constants `Cpack, ε₀ > 0` such that for every integer `k ≥ 3` and every
`0 < ε ≤ ε₀` there is a finite set `X ⊆ Δ_k` with `|X| ≥ 2^{-Cpack k} ε^{-(k-2)/2}` (143), whose
points satisfy `7/(8k) ≤ x_y ≤ 9/(8k)`, `x_1 ≤ 15/(16k)` (144), `‖x - v̄‖₂² = 1/(256k)` (145) and,
for distinct points, `⟨x - v̄, x' - v̄⟩ ≤ (1 - 8000ε)/(256k)` (146). -/
theorem lemma_B_2 :
    ∃ Cpack ε₀ : ℝ, 0 < Cpack ∧ 0 < ε₀ ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ X : Finset (Fin k → ℝ), IsSimplexPacking Cpack k ε X := by sorry

end MulticlassOmni.Lipschitz
