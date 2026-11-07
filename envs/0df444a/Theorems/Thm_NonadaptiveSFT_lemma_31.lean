-- Prove2me | Theorems.Thm_NonadaptiveSFT_lemma_31
-- name    : NonadaptiveSFT.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:02.415739+00:00
-- url     : https://prove2.me/theorems/5da0eb46-9f64-4655-bc85-864509125fe8
-- title:
--   Lemma 31 — hard-thresholding stability: $\|\widehat X-H_k(\widetilde X^{pre})\|_2^2\le\sigma_k^2+4\sqrt k\,\sigma_k\Delta+5k\Delta^2$
-- statement:
--   For any signal $X$ on $G$, any $\widetilde X^{pre}\in\mathbb C^G$ and $1\le k<N$, with $\Delta=\|\widehat X-\widetilde X^{pre}\|_\infty$,
--
--   $$\|\widehat X-H_k(\widetilde X^{pre})\|_2^2\le\sigma_k(\widehat X)_2^2+4\sqrt k\,\sigma_k(\widehat X)_2\,\Delta+5k\Delta^2.\tag{58}$$
--
--   It converts the coordinatewise guarantee into the $(1+\varepsilon)$ $\ell_2/\ell_2$ guarantee of the main theorem.
--
--   **Formalization Note** Stated for vectors on any finite index set with any fixed tie order.
--
--   Differences from the source:
--   - generalization: X̂ and X̃^pre on G with the fixed order on G → any vectors Y, Y^pre on any finite index type with any injective tie key; reason: the proof uses only the selection rule of H_k; the paper's case is ι = G, Y = X̂
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Lemma 31 and eq. (58), p.46 (PDF p.48)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Fourier

namespace NonadaptiveSFT

/-- **Lemma 31** (Hard-thresholding stability), (58), p.46 (PDF p.48).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

For any signal `X` on `G`, any `X̃^pre ∈ ℂ^G` and `1 ≤ k < N`, with `Δ = ‖X̂ − X̃^pre‖_∞`,
`‖X̂ − H_k(X̃^pre)‖₂² ≤ σ_k(X̂)₂² + 4√k σ_k(X̂)₂ Δ + 5kΔ²`.

**Formalization Note.** Stated for any finite index type `ι` with any fixed tie order (an injective
key), and any vectors `Y` (in the role of `X̂`) and `Ypre`; the paper's case is `ι = G`, `Y = X̂`, with
its fixed order on `G`. `H_k` is `NonadaptiveSFT.Hk` and `σ_k(Y)₂ = ‖Y − H_k(Y)‖₂`. -/
theorem lemma_31 {ι : Type*} [Fintype ι] (key : ι → ℕ) (hkey : Function.Injective key)
    (Y Ypre : ι → ℂ) (k : ℕ) (hk : 1 ≤ k) (hkN : k < Fintype.card ι) :
    l2 (Y - Hk key k Ypre) ^ 2 ≤
      sigma key k Y ^ 2 + 4 * Real.sqrt k * sigma key k Y * linf (Y - Ypre) +
        5 * k * linf (Y - Ypre) ^ 2 := by sorry

end NonadaptiveSFT
