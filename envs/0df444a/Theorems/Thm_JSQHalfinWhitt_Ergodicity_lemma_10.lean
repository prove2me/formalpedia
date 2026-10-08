-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Ergodicity_lemma_10
-- name    : JSQHalfinWhitt.Ergodicity.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:28.57375+00:00
-- url     : https://prove2.me/theorems/16dca966-050f-4ae4-bce6-61dd26ea6cf9
-- title:
--   Lemma 10 — the fluid hitting time τ̃^{(κ)} extends to x₂ = 0, vanishes on x₁ = −κ/√n, and has the partials (C.5)
-- statement:
--   Fix an integer $n\ge1$, $\beta>0$ and $\kappa>\beta$, and let $\tilde\tau^{(\kappa)}$ be the hitting time (C.1),
--   $$\tilde\tau^{(\kappa)}(x)=\frac{-(x_1+\beta/\sqrt n)}{x_2}-W\Big(\frac{(\kappa-\beta)/\sqrt n}{x_2}\,e^{-(x_1+\beta/\sqrt n)/x_2}\Big),\qquad x_1\le-\kappa/\sqrt n,\ x_2>0,$$
--   where $W$ is the principal branch of the Lambert W function. Then:
--
--   1. (C.3) for every $x_1\le-\kappa/\sqrt n$,
--   $$\lim_{x_2\downarrow0}\tilde\tau^{(\kappa)}(x_1,x_2)=\log\Big(\frac{-\sqrt n x_1-\beta}{\kappa-\beta}\Big),$$
--   so $\tilde\tau^{(\kappa)}$ extends continuously to $x_2=0$ (the extension takes this value);
--   2. (C.4) $\tilde\tau^{(\kappa)}(-\kappa/\sqrt n,x_2)=0$ for all $x_2\ge0$;
--   3. (C.5) for $x_1\le-\kappa/\sqrt n$ and $x_2\ge0$ the partial derivatives exist, as one-sided derivatives on the lines $\{x_1=-\kappa/\sqrt n\}$ and $\{x_2=0\}$, and
--   $$\tilde\tau^{(\kappa)}_1(x)=-\frac{e^{-\tilde\tau^{(\kappa)}(x)}}{x_2e^{-\tilde\tau^{(\kappa)}(x)}+(\kappa-\beta)/\sqrt n},\qquad \tilde\tau^{(\kappa)}_2(x)=\tilde\tau^{(\kappa)}_1(x)\,\tilde\tau^{(\kappa)}(x).$$
--
--   The extension and the derivative formulas are what make $f^{(1)}$ of Lemma 11 well defined and continuously differentiable up to the boundary $\{x_2=0\}$ of $\Omega$.
--
--   **Formalization Note** The printed (C.5) reads $\tilde\tau^{(\kappa)}_2=-\tilde\tau^{(\kappa)}_1\tilde\tau^{(\kappa)}$. Implicit differentiation of the defining identity (C.2), $-\beta/\sqrt n+(x_1+\beta/\sqrt n)e^{-\tilde\tau}+x_2\tilde\tau e^{-\tilde\tau}=-\kappa/\sqrt n$, gives $\tilde\tau_2=\tilde\tau\,\tilde\tau_1$, the same relation as Lemma 6's (4.12) on p. 13, and a numerical check of (C.1) confirms it (e.g. $n=4$, $\beta=1$, $\kappa=1.5$, $x=(-2,0.7)$: $\tilde\tau_2\approx-0.754=\tilde\tau_1\tilde\tau$). The printed minus sign is a misprint, and the corrected identity is stated. The partials are `HasDerivWithinAt` of the coordinate sections within `Set.Iic (−κ/√n)` (in $x_1$) and `Set.Ici 0` (in $x_2$), which are the one-sided derivatives on the boundary lines. The value of $\tilde\tau^{(\kappa)}$ at $x_2=0$ is fixed by the definition; (C.3) is the statement that the values for $x_2>0$ converge to it.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 36, Lemma 10, (C.3)–(C.5); (C.1)–(C.2) on p. 35

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Ergodicity_Candidates

namespace JSQHalfinWhitt.Ergodicity

open Filter Topology

/-- Lemma 10, p. 36 (with (C.5)'s second identity corrected to `τ̃₂ = τ̃₁ τ̃`, see the item's
Formalization Note). Let `n ≥ 1`, `β > 0` and `κ > β`.
(C.3) for `x₁ ≤ −κ/√n`, `τ̃^{(κ)}(x₁, x₂) → log((−√n x₁ − β)/(κ − β))` as `x₂ ↓ 0`;
(C.4) `τ̃^{(κ)}(−κ/√n, x₂) = 0` for `x₂ ≥ 0`;
(C.5) for `x₁ ≤ −κ/√n`, `x₂ ≥ 0`, the partial derivatives exist as derivatives within
`{x₁ ≤ −κ/√n}` resp. `{x₂ ≥ 0}` (one-sided on the boundary), with
`τ̃₁ = −e^{−τ̃}/(x₂e^{−τ̃} + (κ − β)/√n)` and `τ̃₂ = τ̃₁ τ̃`. -/
theorem lemma_10 (n : ℕ) (hn : 0 < n) (β κ : ℝ) (hβ : 0 < β) (hκ : β < κ) :
    (∀ x1 : ℝ, x1 ≤ -κ / Real.sqrt n →
      Tendsto (fun x2 => tauTilde n β κ (x1, x2)) (𝓝[>] 0)
        (𝓝 (Real.log ((-Real.sqrt n * x1 - β) / (κ - β))))) ∧
    (∀ x2 : ℝ, 0 ≤ x2 → tauTilde n β κ (-κ / Real.sqrt n, x2) = 0) ∧
    (∀ x1 x2 : ℝ, x1 ≤ -κ / Real.sqrt n → 0 ≤ x2 →
      HasDerivWithinAt (fun s => tauTilde n β κ (s, x2))
          (-Real.exp (-tauTilde n β κ (x1, x2)) /
            (x2 * Real.exp (-tauTilde n β κ (x1, x2)) + (κ - β) / Real.sqrt n))
          (Set.Iic (-κ / Real.sqrt n)) x1 ∧
        HasDerivWithinAt (fun s => tauTilde n β κ (x1, s))
          (-Real.exp (-tauTilde n β κ (x1, x2)) /
              (x2 * Real.exp (-tauTilde n β κ (x1, x2)) + (κ - β) / Real.sqrt n) *
            tauTilde n β κ (x1, x2))
          (Set.Ici 0) x2) := by sorry

end JSQHalfinWhitt.Ergodicity
