-- Prove2me | Theorems.Thm_MaxEntSampling_lemma_5
-- name    : MaxEntSampling.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:32.841376+00:00
-- url     : https://prove2.me/theorems/50c5a33a-a286-4caa-82e4-49485e332c6a
-- title:
--   Lemma 5 — $\sum_{|S|=s}\prod_{i\in S}\hat x_i\det^s(V_SV_S^\top)\ge\exp\Gamma_s\bigl(\sum_i\hat x_iv_iv_i^\top\bigr)$
-- statement:
--   Let $V\in\mathbb R^{d\times n}$ have rank $d$ (so $X=V^\top V\succeq0$ has rank $d$), with columns $v_i$, let $s\in[d]$, and let $\hat x\in\mathbb R^n_+$. Then
--
--   $$
--   \sum_{S\in\binom{[n]}{s}}\prod_{i\in S}\hat x_i\,{\det}^s(V_SV_S^\top) \;\ge\; \exp\Bigl[\Gamma_s\Bigl(\sum_{i\in[n]}\hat x_iv_iv_i^\top\Bigr)\Bigr].
--   $$
--
--   This compares the unnormalized expectation of the sampling law (13) with the relaxation objective; it is the first inequality in the proof of Theorem 5.
--
--   **Formalization Note** The inequality is stated in logarithmic form, $\log(\text{left side})\ge\Gamma_s(\cdot)$, in the extended reals with $\log0=-\infty$.
--
--   Differences from the source:
--   - encoding: A ≥ exp[Γ_s(…)] → ENNReal.log (ENNReal.ofReal A) ≥ Γ_s(…) in EReal; reason: A ≥ 0 and exp is an order isomorphism from [−∞, ∞) onto [0, ∞), so the two forms are equivalent
--   - encoding: an n × n matrix X ⪰ 0 of rank d with X = VᵀV, V ∈ ℝ^{d×n} → V with V.rank = d; reason: X enters only through V, and rank X = rank V
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Lemma 5, p.14 (PDF p.14)

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model
import Definitions.Def_MaxEntSampling_detTop
import Definitions.Def_MaxEntSampling_GammaS

open Finset

namespace MaxEntSampling

open PropVolSampling.Reduction

/-- **Lemma 5: `Σ_{|S|=s} ∏_{i∈S} x̂_i det^s(V_S V_Sᵀ) ≥ exp Γ_s(Σ_i x̂_i v_i v_iᵀ)`.**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Lemma 5, p.14 (PDF p.14): "Given an n × n matrix X ⪰ 0 of rank d such that
X = V^⊤V with V ∈ R^{d×n} and a vector x̂ ∈ R^n_+, then we have
Σ_{S∈C([n],s)} ∏_{i∈S} x̂i det^s(V_S V_S^⊤) ≥ exp[Γs(Σ_{i∈[n]} x̂i vi vi^⊤)]."

For `V ∈ ℝ^{d×n}` of rank `d`, `s ∈ [d]` and every `x̂ ∈ ℝⁿ₊`,
`log ( Σ_{|S| = s} ∏_{i∈S} x̂_i · det^s(Σ_{i∈S} v_i v_iᵀ) ) ≥ Γ_s(Σ_i x̂_i v_i v_iᵀ)`.

**Formalization Note.** The inequality `A ≥ exp Γ` is stated in logarithmic form
`log A ≥ Γ` in `EReal` (`log = ENNReal.log ∘ ENNReal.ofReal`, `log 0 = −∞`); since `A ≥ 0` and
`exp` is an order isomorphism from `[−∞, ∞)` onto `[0, ∞)`, the two forms are equivalent.
`V_S V_Sᵀ = Σ_{i∈S} v_i v_iᵀ` is `gram V S`, `Σ_i x̂_i v_i v_iᵀ` is `weightedGram V x`, and
`∏_{i∈S} x̂_i` is `xPow x S`. The matrix `X = VᵀV` of the page enters only through `V`. -/
theorem lemma_5 {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (s : ℕ) (hs1 : 1 ≤ s) (hsd : s ≤ d)
    (hrank : V.rank = d) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    GammaS s (weightedGram V x) ≤
      ENNReal.log (ENNReal.ofReal
        (∑ S ∈ (univ : Finset (Fin n)).powersetCard s, xPow x S * detTop s (gram V S))) := by sorry

end MaxEntSampling
