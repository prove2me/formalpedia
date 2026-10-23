-- Prove2me | Theorems.Thm_LoockCVQEC_RepCode_eq_10_error_probability_gamma_cubed
-- name    : LoockCVQEC.RepCode.eq_10_error_probability_gamma_cubed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:12.107819+00:00
-- url     : https://prove2.me/theorems/d0ee0fc7-cfb4-42c2-9f80-5244b77aa236
-- title:
--   Eq. (10), p. 4 — with infinite squeezing the output is (1−γ³)W_in + γ³W_in(x₁−√3x̄₂, p₁); fidelity → 1−γ³+γ³e^{−3x̄₂²} (corrected: exact comparison with direct transmission)
-- statement:
--   Let $W_{\mathrm{in}}$ be the coherent input with mean $(\bar x_1,\bar p_1)$, let each of the three modes suffer independently an x-displacement by $\bar x_2>0$ with probability $\gamma\in(0,1)$, and run the protocol: encode with two x-squeezed ancillas (squeezing $r$) by the tritter, transmit, invert the tritter, x-homodyne modes 2 and 3, displace mode 1 by $\varphi(x_2,x_3)$, and average over the outcomes. Write $W_r$ for the resulting state of mode 1 and $F(W)=\pi\int W_{\mathrm{in}}W$ for the fidelity with the input.
--
--   Assume the feedforward $\varphi:\mathbb R^2\to\mathbb R$ is measurable and applies the paper's correction near each syndrome: for every error pattern $S\ne\{1,2,3\}$ and every $(x_2,x_3)$ with
--   $$\big(x_2-\sigma_2(S)\big)^2+\big(x_3-\sigma_3(S)\big)^2<\bar x_2^2/6,$$
--   $\varphi(x_2,x_3)$ equals the feedforward $\varphi_S(x_2,x_3)$ of Eq. (9) for pattern $S$ (the radius $\bar x_2/\sqrt6$ is half the minimal distance between distinct syndromes, so these discs are disjoint; nearest-syndrome decoding is one such $\varphi$). Then:
--
--   1. **Eq. (10).** For all $x_1,p_1$, as $r\to\infty$,
--   $$W_r(x_1,p_1)\longrightarrow(1-\gamma^3)\,W_{\mathrm{in}}(x_1,p_1)+\gamma^3\,W_{\mathrm{in}}(x_1-\sqrt3\,\bar x_2,p_1).$$
--   2. **Fidelity.** As $r\to\infty$,
--   $$F(W_r)\longrightarrow1-\gamma^3+\gamma^3e^{-3\bar x_2^2},$$
--   which is at least $1-\gamma^3$, with the excess $\gamma^3e^{-3\bar x_2^2}$ the paper mentions for small $\bar x_2$.
--   3. **Comparison with direct transmission (corrected).** The limiting fidelity exceeds the exact fidelity of direct transmission, $F_{\mathrm{direct}}=1-\gamma+\gamma e^{-\bar x_2^2}$, if and only if
--   $$\gamma^2\big(1+e^{-\bar x_2^2}+e^{-2\bar x_2^2}\big)<1 .$$
--
--   The paper states that the encoded scheme beats direct transmission with $F_{\mathrm{direct}}=1-\gamma$ "for any $0<\gamma<1$", i.e. that the error probability drops from $\gamma$ to $\gamma^3$. With the exact direct fidelity this holds for every $\gamma\le1/\sqrt3$ and, for each $\gamma<1$, once $\bar x_2$ is large (the paper's standing "$\bar x_2\gg1$"), but not in general: $\gamma=0.9$, $\bar x_2=0.5$ gives $0.615$ against $0.801$. Part 3 is the exact form of the comparison.
--
--   **Formalization Note** $W_r$ is computed from the protocol (product state, tritter, three channels, inverse tritter, four-dimensional Bochner integral over $((x_2,x_3),(p_2,p_3))$). The feedforward sees only $(x_2,x_3)$; the discs use the Euclidean distance, not Mathlib's sup metric on $\mathbb R\times\mathbb R$ (sup-metric balls of this radius overlap). Mode/channel $j$ is Lean index $j-1$. The fidelity formula is the overlap with the pure input in the units of Eq. (2).
--
--   Differences from the source:
--   - correction: the encoded scheme beats direct transmission "with F_direct = 1 − γ" for any 0 < γ < 1 → limiting encoded fidelity > exact F_direct = 1 − γ + γe^{−x̄₂²} ↔ γ²(1 + e^{−x̄₂²} + e^{−2x̄₂²}) < 1; reason: with the exact direct fidelity the claim is false: γ = 0.9, x̄₂ = 0.5 gives 0.615 < 0.801; it holds for γ ≤ 1/√3 and, for each γ < 1, for x̄₂ ≫ 1, the paper's assumption
--   - reading: "a fidelity of at least 1 − γ³ can be achieved", exceeding it for small x̄₂; fidelity is not defined → F(W_r) → 1 − γ³ + γ³e^{−3x̄₂²} with F(W) = π∫W_in W; reason: π∫W_in W is ⟨ψ|ρ|ψ⟩ for the pure coherent input in the units of Eq. (2); the exact limit implies "at least 1 − γ³"
--   - reading: the recovery displacement of mode 1 "depends on the syndrome measurement results"; decision regions are not stated → every measurable φ(x₂, x₃) that equals the page's φ_S on the open Euclidean disc of radius x̄₂/√6 around σ(S), for each S ≠ {1,2,3}; reason: the discs are disjoint (half the minimal syndrome distance), nearest-syndrome decoding satisfies it, and the page applies no correction for the all-error case
--   - reading: the tritter is "a sequence of two beam splitters with transmittances 1 : 2 and 1 : 1"; its matrix is not printed → the orthogonal matrix D with rows (1,1,1)/√3, (√(2/3), −1/√6, −1/√6), (0, 1/√2, −1/√2); encode W ↦ W(Dx, Dp), decode W ↦ W(Dᵀx, Dᵀp); reason: this D reproduces Eq. (6) and every term, with signs, of Eq. (8) on the page
--   - encoding: modes and channels numbered 1, 2, 3 → Fin 3, Lean index j − 1 for the paper's mode j; reason: Lean convention; same instances
-- source:
--   van Loock, A note on quantum error correction with continuous variables, arXiv:0811.3616v1, p. 4, Eq. (10) and the following paragraph

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

namespace LoockCVQEC.RepCode

open Real MeasureTheory Filter Topology

theorem eq_10_error_probability_gamma_cubed (xb pb d γ : ℝ) (hd : 0 < d)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hff : ∀ S : Finset (Fin 3), S ≠ Finset.univ → ∀ y2 y3 : ℝ,
      (y2 - (syndrome d S).1) ^ 2 + (y3 - (syndrome d S).2) ^ 2 < d ^ 2 / 6 →
        φ y2 y3 = paperFeedforward S y2 y3) :
    (∀ x1 p1 : ℝ, Tendsto (fun r : ℝ => output xb pb r γ d φ x1 p1) atTop
        (𝓝 ((1 - γ ^ 3) * inW xb pb x1 p1 + γ ^ 3 * inW xb pb (x1 - √3 * d) p1)))
    ∧ Tendsto (fun r : ℝ => fidelity xb pb (output xb pb r γ d φ)) atTop
        (𝓝 (1 - γ ^ 3 + γ ^ 3 * exp (-3 * d ^ 2)))
    ∧ (fidelity xb pb (directOut γ d (inW xb pb)) < 1 - γ ^ 3 + γ ^ 3 * exp (-3 * d ^ 2) ↔
        γ ^ 2 * (1 + exp (-d ^ 2) + exp (-2 * d ^ 2)) < 1) := by sorry

end LoockCVQEC.RepCode
