-- Prove2me | Theorems.Thm_KelnerLinSolve_lemma_3_4
-- name    : KelnerLinSolve.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:33.722674+00:00
-- url     : https://prove2.me/theorems/262437c5-d517-48b7-b274-900391b7bb12
-- title:
--   Lemma 3.4 (Rounding certificate) — the bound (7), the test (8), and when the test passes
-- statement:
--   Let $A_0\in\mathbb R^{n\times n}$ and $b_0\in\mathbb R^n$ satisfy $\tfrac12\le\max_{i,j}|(A_0)_{ij}|\le1$ and $\tfrac12\le\|b_0\|_\infty\le1$. For an integer $h\ge1$ put $\ell=\lceil\log_2n\rceil$, $S=2^h$, $C=\mathrm{round}(SA_0)$, $d=\mathrm{round}(Sb_0)$, $R=2^{h+\ell+1}$ and $y=R(I+RC)^{-1}d$, rounding entries to nearest with a fixed tie rule. For a power of two $P\ge1$ let $\hat y = P^{-1}\mathrm{round}(Py)$. Then
--
--   $$
--   \frac{\|A_0\hat y-b_0\|_2}{\|b_0\|_2}\le\frac{2n^2(\|y\|_\infty+1)}{S}+\frac{n^2}{P}. \tag{7}
--   $$
--
--   Moreover, for $0<\varepsilon\le1$:
--
--   1. if $P\ge4n^2/\varepsilon$, the test $8n^2(\|y\|_\infty+1)\le\varepsilon S$ (8) certifies $\|A_0\hat y-b_0\|_2/\|b_0\|_2\le\varepsilon/2$;
--   2. if $A_0$ is nonsingular and $S\ge64\kappa_2(A_0)n^3/\varepsilon$, the test (8) holds.
--
--   $A_0$ may be singular in (7) and in item 1, and $C$ may be singular. The lemma is the computable certificate that lets the solver search for the precision without knowing $\kappa_2$.
--
--   Differences from the source:
--   - encoding: round to nearest with a fixed tie rule, preserving zero entries → any `rnd : ℝ → ℤ` with |rnd x − x| ≤ 1/2; reason: such maps are exactly the nearest roundings with some fixed tie rule, and they fix 0
--   - encoding: a power of two P ≥ 1 → P = 2^p with p : ℕ; reason: same set
--   - encoding: y = R(I + RC)⁻¹d → `trialY`, inverse over ℝ; reason: I + RC has integer determinant ≡ 1 (mod R), so this is the true inverse
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Lemma 3.4, pp.11–12

import Mathlib
import Definitions.Def_KelnerLinSolve_kappa2
import Definitions.Def_KelnerLinSolve_trialY

open Matrix

namespace KelnerLinSolve

/-- **Lemma 3.4 (Rounding certificate)**, Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit
Operations*, STOC 2027 submission (sha256 d1af55cb…), pp.11–12. "Let `A₀ ∈ ℝ^{n×n}` and `b₀ ∈ ℝⁿ`
satisfy `1/2 ≤ max_{i,j} |(A₀)_{ij}| ≤ 1`, `1/2 ≤ ‖b₀‖_∞ ≤ 1`. For an integer `h ≥ 1`, put
`ℓ = ⌈log₂ n⌉`, `S = 2^h`, and `C = round(SA₀)`, `d = round(Sb₀)`, `R = 2^{h+ℓ+1}`,
`y = R(I + RC)⁻¹d`. Round entries to nearest with a fixed tie rule, preserving zero entries. For a
power of two `P ≥ 1`, let `ŷ = P⁻¹ round(Py)`. Then
`‖A₀ŷ − b₀‖₂/‖b₀‖₂ ≤ 2n²(‖y‖_∞ + 1)/S + n²/P`. (7) In particular, for `0 < ε ≤ 1` and
`P ≥ 4n²/ε`, the test `8n²(‖y‖_∞ + 1) ≤ εS` (8) certifies relative residual at most `ε/2`. If `A₀` is
nonsingular, the test holds for `S ≥ 64κ₂(A₀)n³/ε`."

Three conjuncts: (7); the certificate; the final assertion. `A₀` may be singular in the first two.

**Formalization Note.** `y = trialY rnd A₀ b₀ h`, computed over `ℝ`; `rnd` is any rounding to nearest
(`IsNearestRounding`), which covers every fixed tie rule and maps `0` to `0`. `P = 2^p` with
`p : ℕ`. `max_{i,j}|·|` is `maxAbsEntry`, `‖·‖_∞` is `infNorm`, `‖·‖₂` is `norm2`, `κ₂` is
`kappa2`. -/
theorem lemma_3_4 {n : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ) (b₀ : Fin n → ℝ)
    (hA : 1 / 2 ≤ maxAbsEntry A₀ ∧ maxAbsEntry A₀ ≤ 1) (hb : 1 / 2 ≤ infNorm b₀ ∧ infNorm b₀ ≤ 1)
    (h : ℕ) (hh : 1 ≤ h) (rnd : ℝ → ℤ) (hrnd : IsNearestRounding rnd) (p : ℕ) :
    let S : ℝ := 2 ^ h
    let P : ℝ := 2 ^ p
    let y : Fin n → ℝ := trialY rnd A₀ b₀ h
    let yhat : Fin n → ℝ := fun i => (rnd (P * y i) : ℝ) / P
    norm2 (A₀ *ᵥ yhat - b₀) / norm2 b₀ ≤ 2 * (n : ℝ) ^ 2 * (infNorm y + 1) / S + (n : ℝ) ^ 2 / P ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → 4 * (n : ℝ) ^ 2 / ε ≤ P → 8 * (n : ℝ) ^ 2 * (infNorm y + 1) ≤ ε * S →
      norm2 (A₀ *ᵥ yhat - b₀) / norm2 b₀ ≤ ε / 2) ∧
    (A₀.det ≠ 0 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 64 * kappa2 A₀ * (n : ℝ) ^ 3 / ε ≤ S →
      8 * (n : ℝ) ^ 2 * (infNorm y + 1) ≤ ε * S) := by sorry

end KelnerLinSolve
