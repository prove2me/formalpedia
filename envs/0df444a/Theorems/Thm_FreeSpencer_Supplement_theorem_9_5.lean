-- Prove2me | Theorems.Thm_FreeSpencer_Supplement_theorem_9_5
-- name    : FreeSpencer.Supplement.theorem_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:33:50.851025+00:00
-- url     : https://prove2.me/theorems/f2e14287-21b8-4813-8a17-549ca39042c2
-- title:
--   Theorem 9.5 — general Tsallis curvature estimate (9.11), (9.12) and the local unconstrained response
-- statement:
--   Let $D\ge1$, $\ell\ge1$, let $\widehat A_1,\dots,\widehat A_\ell$ be real symmetric $D\times D$ contractions, and let $0\preceq C\preceq I_\ell$. Fix $0<q\le\tfrac12$, $\theta>0$ and $L>0$, and consider the Tsallis potential
--   $$E_{q,\theta}(H,C)=\max_{S\succeq0,\ \operatorname{Tr}S=1}\Big\{\operatorname{Tr}(HS)+2F(S,\eta_C(S))+\frac{\theta}{1-q}\operatorname{Tr}S^{1-q}\Big\}.$$
--
--   1. Let $H$ be real symmetric and let $S$ be the optimal density, with $\eta_C(S)$ positive definite. Let $J(u,u)=\frac12D_H^2E[\widehat A(u),\widehat A(u)]$ and let $\Gamma$ be the covariance derivative. If $\Gamma|_{\operatorname{ran}C}\preceq\frac{L}{\sqrt\ell}I$, then for every $c>0$
--   $$\operatorname{Tr}(CJ)\le2\sqrt\ell+\frac{4c^q+2L^2c^{q-2}}{\theta q}\,\ell^{1-q},\qquad(9.11)$$
--   and in particular (with $c=L$)
--   $$\operatorname{Tr}(CJ)\le2\sqrt\ell+\frac{6L^q}{\theta q}\,\ell^{1-q}.\qquad(9.12)$$
--   2. The same two bounds hold for the local unconstrained response at any positive definite $S$ with $\operatorname{Tr}S\le1$: if $\eta_C(S)\succ0$, $Z\succ0$ solves $Z\eta_C(S)Z=S$, and $\Gamma(S)(u,u)=\operatorname{Tr}(S\widehat A(u)Z\widehat A(u))\le\frac{L}{\sqrt\ell}\|u\|^2$ for $u\in\operatorname{ran}C$, then with $B'_a=\widehat A(C^{1/2}e_a)$ and $\mathcal H^{\mathrm{original}}=\mathcal H_f^{\mathrm{original}}+\mathcal H_{q,\theta}^{\mathrm{original}}$, the symmetric solutions $Y_a$ of $\mathcal H^{\mathrm{original}}(Y_a)=B'_a$ exist and
--   $$\sum_a\tfrac12\langle B'_a,(\mathcal H^{\mathrm{original}})^{-1}B'_a\rangle=\sum_a\tfrac12\operatorname{Tr}(B'_aY_a)$$
--   satisfies (9.11) for every $c>0$ and (9.12).
--
--   At $q=1/2$ the estimate (9.12) is the square-root curvature bound of Theorem 6.5; for general $q$ it is the response bound of the rectangular potentials used for $m>n$.
--
--   **Formalization Note** $E_{q,\theta}$, $J$, $\Gamma$, $\operatorname{Tr}(CJ)$ and the no-spike condition are the published `pot`, `halfCurv`, `covForm`, `TrCJ`, `NoSpike` at $\kappa=0$; "the optimal density" is any maximizer. Powers $c^q$, $c^{q-2}$, $L^q$, $\ell^{1-q}$ are real powers. The response is written through symmetric solutions $Y_a$ (existence asserted; the bound is asserted for every such choice).
--
--   Differences from the source:
--   - encoding: (H^original)⁻¹(B'_a) → symmetric solutions Y_a of H^original(Y_a) = B'_a, existence asserted and the bound stated for every such solution; reason: the operator is inverted on symmetric matrices, where the solution is unique, so this is the same quantity.
--   - encoding: L unrestricted in "Γ|_{ran C} ⪯ (L/√ℓ) I" → hypothesis L > 0; reason: Γ(u,u) = ‖Z^{1/2}Â(u)S^{1/2}‖² ≥ 0, so L ≤ 0 forces Â(C^{1/2}e_a) = 0 for every a, hence η_C = 0, contradicting η_C(S) ≻ 0 (D ≥ 1); L > 0 excludes only these vacuous cases (and the undefined L^q for L < 0), and c = L > 0 is needed for (9.12).
--   - reading: "The same bound holds for the local unconstrained response" → both (9.11) for every c > 0 and (9.12) for the response; reason: the stronger reading, which the proof (p.62, last paragraph: "every algebraic and trace estimate above also holds") establishes; (9.12) alone follows from it.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 9.5, p.62; parameters pp.56, 58; local unconstrained response p.31 and Lemma 5.5, p.37

import Mathlib
import Definitions.Def_FreeSpencer_Supplement_opHq
import Definitions.Def_FreeSpencer_KrausFacts
import Definitions.Def_FreeSpencer_covForm
import Definitions.Def_FreeSpencer_pot
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer.Supplement

open FreeSpencer

/-- **Theorem 9.5** (General Tsallis curvature estimate), (9.11), (9.12) and the closing sentence on the
local unconstrained response, for every `0 < q ≤ 1/2`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914
(held file sha256 e1c1ba14…), Theorem 9.5, p.62; parameters fixed on pp.56, 58; local unconstrained
response p.31 and Lemma 5.5, p.37.

**Formalization Note** `E_{q,θ}` is the published `pot q θ 0`; `J`, `Γ`, `Tr(CJ)` and the no-spike
condition are the published `halfCurv`, `covForm`, `TrCJ`, `NoSpike` at `κ = 0`. "The optimal density" is
any maximizer (`IsMaximizer`); the hypothesis is that `η_C(S)` is positive definite there. `L > 0` as in
Theorem 6.5. Powers `c^q`, `c^{q-2}`, `L^q`, `ℓ^{1-q}` are real powers. In the second clause `S ≻ 0` with
`Tr S ≤ 1` is arbitrary, `Z ≻ 0` solves `Z η_C(S) Z = S`, `Γ(S)` is `gammaAt`, and the local unconstrained
response `∑ₐ ½⟨B'ₐ, (H^original)⁻¹ B'ₐ⟩` is written through symmetric solutions `Yₐ` of
`H^original(Yₐ) = B'ₐ`, with `H^original = H_f^original + H_{q,θ}^original` (`opHqFull`): such solutions
exist, and every choice satisfies both bounds. -/
theorem theorem_9_5 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ℓ : ℕ}
    (Ah : Fin ℓ → Matrix ι ι ℝ) (hAh : IsContrFam Ah) (hℓ : 1 ≤ ℓ) (q θ L : ℝ) (hq : 0 < q)
    (hq2 : q ≤ 1 / 2) (hθ : 0 < θ) (hL : 0 < L) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) (hC : IsCov C) :
    (∀ H S : Matrix ι ι ℝ, H.IsSymm → IsMaximizer q θ 0 Ah H C S → (covMap Ah C S).PosDef →
      NoSpike q θ 0 Ah H C (L / Real.sqrt ℓ) →
      (∀ c : ℝ, 0 < c → TrCJ q θ 0 Ah H C ≤
          2 * Real.sqrt ℓ + (4 * c ^ q + 2 * L ^ 2 * c ^ (q - 2)) / (θ * q) * (ℓ : ℝ) ^ (1 - q)) ∧
      TrCJ q θ 0 Ah H C ≤ 2 * Real.sqrt ℓ + 6 * L ^ q / (θ * q) * (ℓ : ℝ) ^ (1 - q)) ∧
    (∀ S Z : Matrix ι ι ℝ, S.PosDef → Matrix.trace S ≤ 1 → (covMap Ah C S).PosDef → Z.PosDef →
      Z * covMap Ah C S * Z = S →
      (∀ u, InRan C u → gammaAt Ah S Z u u ≤ L / Real.sqrt ℓ * (u ⬝ᵥ u)) →
      (∃ Y : Fin ℓ → Matrix ι ι ℝ,
        ∀ a, (Y a).IsSymm ∧ opHqFull q θ Ah C S Z (covMap Ah C S) (Y a) = krausB Ah C a) ∧
      ∀ Y : Fin ℓ → Matrix ι ι ℝ,
        (∀ a, (Y a).IsSymm ∧ opHqFull q θ Ah C S Z (covMap Ah C S) (Y a) = krausB Ah C a) →
        (∀ c : ℝ, 0 < c → ∑ a, (1 / 2) * Matrix.trace (krausB Ah C a * Y a) ≤
          2 * Real.sqrt ℓ + (4 * c ^ q + 2 * L ^ 2 * c ^ (q - 2)) / (θ * q) * (ℓ : ℝ) ^ (1 - q)) ∧
        ∑ a, (1 / 2) * Matrix.trace (krausB Ah C a * Y a) ≤
          2 * Real.sqrt ℓ + 6 * L ^ q / (θ * q) * (ℓ : ℝ) ^ (1 - q)) := by sorry

end FreeSpencer.Supplement
